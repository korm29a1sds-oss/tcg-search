#!/usr/bin/env python3
"""
TCG 검색 수요 수집기 (네이버 검색광고 API · keywordstool)

keywords.txt의 키워드 월간 검색량과 연관 검색어를 수집해 data/에 저장한다.
  data/history/YYYY-MM-DD.json  하루치 스냅샷 (KST 날짜, 같은 날 재실행 시 덮어씀, 400일 보관)
  data/latest.json              최신 스냅샷 + 비교 결과(diffs)
  data/latest.md                아침 브리핑용 한국어 요약 (약 60줄)
  data/status.json              마지막 실행 결과 {date, status: ok|partial|failed, reason}

스냅샷 항목 형식 (seeds/related 공통, schema_version 1)
  pc, mobile     월간 검색량 정수 (네이버가 "< 10"으로 준 값은 0)
  total          pc + mobile
  has_lt10       pc 또는 mobile 중 하나라도 "< 10"이면 true
  pc_lt10, mobile_lt10   해당 값이 "< 10"일 때만 존재 (true)
  compIdx        광고 경쟁 정도 (높음/중간/낮음)
  related는 검색량 상위 500개만 저장하고, 필터를 통과한 전체 이름은 related_keys에 둔다.
  failed_seeds = 요청 실패, no_data_seeds = 이번 실행에서 값이 없는 seed(실패 포함),
  missing_seeds = 이전 스냅샷엔 있었는데 오늘 없는 seed. 표준 라이브러리만 사용 (Python 3.11+).

사용법
  python3 collect.py                  수집
  python3 collect.py --skip-if-done   status.json이 오늘 'ok'이면 바로 종료 (예약 재시도용)
  python3 collect.py --selftest       오프라인 자체 점검 (네트워크 사용 안 함)

환경 변수
  NAVER_CUSTOMER_ID, NAVER_ACCESS_LICENSE, NAVER_SECRET_KEY   (필수)
  NAVER_API_BASE        (선택) API 주소. 기본 https://api.searchad.naver.com (모의 서버 테스트용)
  COLLECT_TODAY         (테스트용) 오늘 날짜(KST)를 YYYY-MM-DD로 강제 지정
  COLLECT_BACKOFF_BASE  (테스트용) 재시도 대기 기본 초 (기본 1.0)

보안: 헤더, 비밀 키, 서명, 요청 URL은 로그/파일에 남기지 않는다. 개수와 오류 코드만 기록한다.
"""

from __future__ import annotations

import base64
import hashlib
import hmac
import http.client
import json
import os
import sys
import tempfile
import time
import traceback
import urllib.error
import urllib.parse
import urllib.request
from datetime import date, datetime, timedelta, timezone
from pathlib import Path

# ── 설정값 ─────────────────────────────────────────────────────────
KST = timezone(timedelta(hours=9))
ROOT = Path(__file__).resolve().parent
KEYWORDS_FILE = ROOT / "keywords.txt"
DATA_DIR = ROOT / "data"

DEFAULT_API_BASE = "https://api.searchad.naver.com"
API_PATH = "/keywordstool"
BATCH_SIZE = 5            # hintKeywords 최대 5개
REQUEST_INTERVAL = 0.5    # 요청 간 대기(초)
MAX_RETRIES = 3           # 429/5xx/네트워크 오류 재시도 횟수
HTTP_TIMEOUT = 20         # 요청 타임아웃(초)
MAX_RETRY_AFTER = 30      # 429 Retry-After 최대 반영(초)
RUN_BUDGET_SEC = 420      # 수집 전체 시간 예산(초) — 워크플로 10분 제한 안에 끝내기 위함

SCHEMA_VERSION = 1
HISTORY_KEEP_DAYS = 400   # 이보다 오래된 history 파일 삭제
RELATED_KEEP = 500        # 저장할 연관 검색어 수 (검색량 상위)
WEEK_AGE = (7, 10)        # 7일 기준: today-10 ~ today-7 사이의 가장 최근 파일
NEW_REL_WINDOW = 7        # 새 연관 검색어: 최근 7일 기록 전체와 비교

RISING_MIN_TOTAL = 100    # 급상승 / 새 연관 검색어의 월간 검색량 하한
RISING_MIN_PCT = 20.0     # 급상승 증가율 하한(%)
NEW_REL_MIN_TOTAL = 100
TOP_N = 10                # latest.md 각 표의 최대 행 수
FAILED_SHOW = 5           # 실패 키워드 표시 개수

REQUIRED_ENV = ("NAVER_CUSTOMER_ID", "NAVER_ACCESS_LICENSE", "NAVER_SECRET_KEY")
WARN = "\N{WARNING SIGN}\N{VARIATION SELECTOR-16}"   # 소스에 보이지 않는 문자를 두지 않으려고 이름으로 표기
FAIL_MARK = "> \N{CROSS MARK}"
FOOTNOTE = "월간 = 최근 30일 합계라 변화가 완만함 · <10 = 네이버가 10 미만으로만 알려줌"


class AuthError(Exception):
    """401/403 — 재시도 없이 즉시 종료."""


class BatchError(Exception):
    """재시도 후에도 실패한 요청."""


class BadRequest(BatchError):
    """HTTP 400 — 여러 키워드 요청이면 1개씩 다시 조회한다."""


def log(msg: str) -> None:
    print(msg, file=sys.stderr, flush=True)


# ── 값 정규화 / keywords.txt ────────────────────────────────────────
def norm(s: str) -> str:
    """비교용 키: 모든 공백 제거 + 소문자."""
    return "".join(s.split()).lower()


def strip_spaces(s: str) -> str:
    return "".join(s.split())


def parse_count(v) -> tuple[int, bool]:
    """검색량 값 → (정수, "< 10" 여부). 알 수 없는 형식은 (0, False)."""
    if isinstance(v, bool):
        return 0, False
    if isinstance(v, (int, float)):
        return int(v), False
    if isinstance(v, str):
        s = v.strip()
        if s.startswith("<"):
            return 0, True
        try:
            return int(float(s.replace(",", ""))), False
        except ValueError:
            pass
    return 0, False


def make_entry(item: dict) -> dict:
    """API 응답 항목 → 저장 항목 (형식은 파일 상단 설명 참고)."""
    pc, pc_lt = parse_count(item.get("monthlyPcQcCnt"))
    mo, mo_lt = parse_count(item.get("monthlyMobileQcCnt"))
    e = {"pc": pc, "mobile": mo, "total": pc + mo, "has_lt10": pc_lt or mo_lt,
         "compIdx": item.get("compIdx")}
    if pc_lt:
        e["pc_lt10"] = True
    if mo_lt:
        e["mobile_lt10"] = True
    return e


def parse_keywords(text: str) -> tuple[list[str], list[str], list[str]]:
    """keywords.txt → (seeds, filters, excludes).

    '#' 주석·빈 줄 무시. '[filter]' / '[exclude]' 줄 이후는 해당 목록.
    seed는 공백 제거 후 중복 제거 (대소문자 무시, 처음 표기 유지). 목록 단어는 norm()으로 저장.
    """
    seeds: list[str] = []
    sections: dict[str, list[str]] = {"[filter]": [], "[exclude]": []}
    seen: set[str] = set()
    cur: list[str] | None = None
    for raw in text.splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if line.lower() in sections:
            cur = sections[line.lower()]
            continue
        k = norm(line)
        if cur is not None:
            if k and k not in cur:
                cur.append(k)
        elif k and k not in seen:
            seen.add(k)
            seeds.append(strip_spaces(line))
    return seeds, sections["[filter]"], sections["[exclude]"]


def is_relevant(keyword: str, filters: list[str], excludes: list[str]) -> bool:
    """제외어가 들어 있으면 탈락, 아니면 필터어 중 하나라도 포함 시 통과 (필터 없으면 통과)."""
    k = norm(keyword)
    if any(x in k for x in excludes):
        return False
    return not filters or any(f in k for f in filters)


# ── 네이버 API 호출 ──────────────────────────────────────────────────
def sign(timestamp: str, method: str, uri: str, secret_key: str) -> str:
    """X-Signature = base64(HMAC-SHA256(secret, "{ts}.{METHOD}.{uri}")). uri는 쿼리 제외 경로."""
    msg = f"{timestamp}.{method}.{uri}".encode("utf-8")
    return base64.b64encode(hmac.new(secret_key.encode("utf-8"), msg, hashlib.sha256).digest()).decode()


def error_summary(e: urllib.error.HTTPError) -> str:
    """오류 응답 본문에서 code/title/message만 뽑아 200자로 자른다 (헤더·URL은 절대 포함 안 함)."""
    try:
        body = json.loads(e.read(4096).decode("utf-8", "replace"))
    except (ValueError, OSError, http.client.HTTPException):
        return ""
    if not isinstance(body, dict):
        return ""
    return ", ".join(f"{k}={body[k]}" for k in ("code", "title", "message")
                     if body.get(k) not in (None, ""))[:200]


def fetch_batch(batch: list[str], creds: dict, api_base: str, backoff_base: float,
                deadline: float) -> list[dict]:
    """키워드 최대 5개를 조회해 keywordList를 반환한다.

    429/5xx/네트워크 오류 → 지수 백오프로 최대 MAX_RETRIES번 재시도 (429는 Retry-After 반영).
    시간 예산(deadline, time.monotonic 기준)을 넘길 것 같으면 재시도 중단.
    401/403 → AuthError, 400 → BadRequest, 그 외 4xx → BatchError (재시도 없음).
    """
    query = urllib.parse.urlencode({"hintKeywords": ",".join(batch), "showDetail": "1"})
    url = f"{api_base.rstrip('/')}{API_PATH}?{query}"
    last_err, retry_after = "", 0.0
    for attempt in range(MAX_RETRIES + 1):
        if attempt:
            wait = max(backoff_base * 2 ** (attempt - 1), retry_after)
            if time.monotonic() + wait + HTTP_TIMEOUT > deadline:
                raise BatchError(f"시간 예산 초과로 재시도 중단 ({last_err})")
            log(f"  재시도 {attempt}/{MAX_RETRIES} ({wait:.1f}초 후)")
            time.sleep(wait)
            retry_after = 0.0
        ts = str(int(time.time() * 1000))  # 요청마다 새 타임스탬프로 서명
        req = urllib.request.Request(url, method="GET", headers={
            "X-Timestamp": ts,
            "X-API-KEY": creds["NAVER_ACCESS_LICENSE"],
            "X-Customer": creds["NAVER_CUSTOMER_ID"],
            "X-Signature": sign(ts, "GET", API_PATH, creds["NAVER_SECRET_KEY"]),
            "Content-Type": "application/json; charset=UTF-8",
            "User-Agent": "tcg-search-collector/1.0",
        })
        try:
            with urllib.request.urlopen(req, timeout=HTTP_TIMEOUT) as resp:
                payload = json.loads(resp.read().decode("utf-8"))
        except urllib.error.HTTPError as e:  # URLError보다 먼저 잡아야 함
            try:
                code = e.code
                if code in (401, 403):
                    raise AuthError(f"인증 실패 (HTTP {code}) — 시크릿 값 확인 필요") from None
                if code == 400:
                    raise BadRequest(f"HTTP 400 {error_summary(e)}".strip()) from None
                if code != 429 and not 500 <= code < 600:
                    raise BatchError(f"HTTP {code}") from None
                last_err = f"HTTP {code}"
                if code == 429:
                    try:
                        retry_after = min(float(e.headers.get("Retry-After") or 0), MAX_RETRY_AFTER)
                    except ValueError:
                        retry_after = 0.0
                continue
            finally:
                e.close()
        except (urllib.error.URLError, http.client.HTTPException, OSError) as e:
            # 연결 실패, 타임아웃, SSL 오류, 읽기 도중 끊김(IncompleteRead) 등 — 재시도
            last_err = f"네트워크 오류: {type(e).__name__}"
            continue
        except ValueError:  # JSON/UTF-8 디코딩 실패
            last_err = "응답 JSON 파싱 실패"
            continue
        items = payload.get("keywordList") if isinstance(payload, dict) else None
        if not isinstance(items, list):
            raise BatchError("응답에 keywordList 없음")
        return items
    raise BatchError(f"재시도 {MAX_RETRIES}회 후 실패 ({last_err})")


def collect(seeds: list[str], filters: list[str], excludes: list[str], creds: dict,
            api_base: str, backoff_base: float) -> dict:
    """seed를 5개씩 조회해 seeds / related(필터 통과 전체) / 실패 목록을 모은다."""
    seed_keys = {norm(s): s for s in seeds}
    seed_data: dict[str, dict] = {}
    related: dict[str, dict] = {}
    related_keys: set[str] = set()
    failed: list[str] = []
    errors: list[str] = []
    queue = [seeds[i:i + BATCH_SIZE] for i in range(0, len(seeds), BATCH_SIZE)]
    requests = ok = 0
    deadline = time.monotonic() + RUN_BUDGET_SEC

    while queue:
        if time.monotonic() > deadline:
            rest = [k for b in queue for k in b]
            log(f"  경고: 시간 예산 초과 — 남은 키워드 {len(rest)}개는 건너뜁니다.")
            failed += rest
            errors.append("시간 예산 초과")
            break
        batch = queue.pop(0)
        if requests:
            time.sleep(REQUEST_INTERVAL)
        requests += 1
        log(f"[{requests}/{requests + len(queue)}] 키워드 {len(batch)}개 조회")
        try:
            items = fetch_batch(batch, creds, api_base, backoff_base, deadline)
        except BatchError as e:
            if isinstance(e, BadRequest) and len(batch) > 1:
                # 잘못된 키워드 하나 때문에 묶음 전체를 잃지 않도록 1개씩 다시 조회
                log(f"  경고: {e} — 키워드를 1개씩 다시 조회합니다.")
                queue[:0] = [[k] for k in batch]
                continue
            log(f"  경고: 실패 — {e}. 다음으로 계속합니다.")
            failed += batch
            errors.append(str(e))
            continue
        ok += 1
        batch_keys = {norm(k) for k in batch}
        kept = 0
        for item in items:
            rel = item.get("relKeyword") if isinstance(item, dict) else None
            if not isinstance(rel, str) or not rel.strip():
                continue
            k = norm(rel)
            if k in seed_keys:
                # 이번 묶음의 힌트이거나 아직 값이 없는 seed면 기록 (다른 묶음 결과로도 채워짐)
                if k in batch_keys or seed_keys[k] not in seed_data:
                    seed_data[seed_keys[k]] = make_entry(item)
            elif k not in related_keys and is_relevant(rel, filters, excludes):
                related_keys.add(k)
                related[strip_spaces(rel)] = make_entry(item)
                kept += 1
        log(f"  결과 {len(items)}개 수신, 연관 검색어 {kept}개 추가")

    # 실패한 묶음의 seed라도 다른 묶음 결과로 값을 얻었다면 실패 목록에서 뺀다
    failed = [s for s in dict.fromkeys(failed) if s not in seed_data]
    return {"seeds": seed_data, "related": related, "failed_seeds": failed,
            "batches": requests, "ok_batches": ok, "errors": errors}


# ── 파일 입출력 ──────────────────────────────────────────────────────
def write_atomic(path: Path, text: str) -> None:
    """같은 폴더 임시 파일에 쓴 뒤 os.replace로 교체 (깨진 파일이 남지 않게)."""
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp = tempfile.mkstemp(dir=path.parent, prefix=f".{path.name}.", suffix=".tmp")
    try:
        with os.fdopen(fd, "w", encoding="utf-8", newline="\n") as f:
            f.write(text)
        os.replace(tmp, path)
    except BaseException:
        try:
            os.unlink(tmp)
        except OSError:
            pass
        raise


def write_json(path: Path, obj) -> None:
    write_atomic(path, json.dumps(obj, ensure_ascii=False, indent=1, sort_keys=True) + "\n")


def load_json(path: Path) -> dict | None:
    try:
        d = json.loads(path.read_text(encoding="utf-8"))
        return d if isinstance(d, dict) else None
    except (OSError, ValueError) as e:
        log(f"경고: {path.name} 읽기 실패 ({type(e).__name__}) — 비교에서 제외")
        return None


def list_history(hist_dir: Path) -> list[tuple[date, Path]]:
    """history 폴더의 (날짜, 경로) 목록, 날짜순. 이름이 날짜가 아닌 파일은 무시."""
    out = []
    for p in hist_dir.glob("*.json") if hist_dir.is_dir() else []:
        try:
            out.append((date.fromisoformat(p.stem), p))
        except ValueError:
            pass
    return sorted(out)


def pick_baselines(history: list[tuple[date, Path]], today: date):
    """(전일 기준, 7일 기준). 전일 = today 이전 가장 최근 파일.
    7일 = today-10 ~ today-7 사이의 가장 최근 파일 (없으면 None)."""
    lo, hi = today - timedelta(days=WEEK_AGE[1]), today - timedelta(days=WEEK_AGE[0])
    prev = next((h for h in reversed(history) if h[0] < today), None)
    week = next((h for h in reversed(history) if lo <= h[0] <= hi), None)
    return prev, week


def prune_history(hist_dir: Path, today: date) -> int:
    cut = today - timedelta(days=HISTORY_KEEP_DAYS)
    n = 0
    for d, p in list_history(hist_dir):
        if d < cut:
            try:
                p.unlink()
                n += 1
            except OSError:
                pass
    return n


def write_status(data_dir: Path, today: date, status: str, reason: str, now: datetime) -> None:
    write_json(data_dir / "status.json", {"date": today.isoformat(), "status": status,
                                          "reason": reason,
                                          "updated_at": now.isoformat(timespec="seconds")})


def write_failure(data_dir: Path, today: date, reason: str, now: datetime) -> None:
    """전체 실패 시: latest.md 맨 위에 실패 안내를 붙이고 이전 본문은 유지.
    (이전 실패 안내는 지움) latest.json은 건드리지 않는다."""
    md = data_dir / "latest.md"
    body = md.read_text(encoding="utf-8").splitlines() if md.is_file() else []
    body = [line for line in body if not line.startswith(FAIL_MARK)]
    while body and not body[0].strip():
        body.pop(0)
    lj = data_dir / "latest.json"
    prev = (load_json(lj) or {}).get("date") if lj.is_file() else None
    tail = f"아래는 {prev} 데이터" if prev and body else "이전 데이터 없음"
    notice = f"{FAIL_MARK} 오늘({today}) 수집 실패 ({reason}) — {tail}"
    body = [f"상태: 실패 — 아래는 {md_date(prev)} 데이터" if line.startswith("상태:") else line
            for line in body]
    write_atomic(md, "\n".join([notice, ""] + body) + "\n")
    write_status(data_dir, today, "failed", reason, now)


# ── 비교(diff) 계산 ─────────────────────────────────────────────────
def by_norm(snap: dict | None, section: str) -> dict:
    return {norm(k): v for k, v in ((snap or {}).get(section) or {}).items()}


def compute_diffs(snap: dict, prev: dict | None, week: dict | None, window: list[dict],
                  related_full: dict | None = None) -> dict:
    """seed별 전일/7일 증감, 급상승, 새 연관 검색어를 계산한다.
    window = 최근 NEW_REL_WINDOW일 스냅샷 목록(날짜순).
    related_full = 상위 500개로 자르기 전 오늘의 연관 검색어 전체 (없으면 snap["related"])."""
    prev_s, week_s = by_norm(prev, "seeds"), by_norm(week, "seeds")
    seeds_diff, rising = {}, []
    for kw, e in snap["seeds"].items():
        k, t = norm(kw), e["total"]
        row = {"total": t, "day_abs": None, "day_pct": None, "week_abs": None, "week_pct": None}
        if k in prev_s:
            b = int(prev_s[k].get("total", 0))
            row["day_abs"], row["day_pct"] = t - b, (round((t - b) / b * 100, 1) if b else None)
        if k in week_s:
            b = int(week_s[k].get("total", 0))
            row["week_abs"], row["week_pct"] = t - b, (round((t - b) / b * 100, 1) if b else None)
            # 0에서 100 이상으로 뛴 경우는 '신규' 급상승으로 맨 앞에
            if t >= RISING_MIN_TOTAL and (b == 0 or row["week_pct"] >= RISING_MIN_PCT):
                rising.append({"keyword": kw, "total": t, "new": b == 0,
                               "week_abs": row["week_abs"], "week_pct": row["week_pct"]})
        seeds_diff[kw] = row
    rising.sort(key=lambda r: (not r["new"], -(r["week_pct"] or 0), -r["total"]))

    # 새 연관 검색어: 최근 7일 기록 어디에도 없던 것. 비교가 불안정하면 목록 대신 안내 문구.
    new_related, note = [], None
    if not window:
        note = "최근 7일 기록이 없어 비교를 건너뛰어요"
    elif window[-1].get("failed_seeds"):
        note = f"{window[-1].get('date')} 수집이 일부 실패해 비교를 건너뛰어요"
    else:
        # 과거 파일의 related_keys(없으면 related 키) + seed 이름 전체와 비교
        seen: set[str] = set()
        for s in window:
            seen.update(norm(k) for k in (s.get("related_keys") or s.get("related") or {}))
            seen.update(norm(k) for k in (s.get("seeds") or {}))
        new_related = sorted(
            ({"keyword": kw, "total": e["total"], "has_lt10": e["has_lt10"],
              "compIdx": e.get("compIdx")}
             for kw, e in (snap["related"] if related_full is None else related_full).items()
             if e["total"] >= NEW_REL_MIN_TOTAL and norm(kw) not in seen),
            key=lambda r: -r["total"])

    return {"prev_date": (prev or {}).get("date"), "week_date": (week or {}).get("date"),
            "seeds": seeds_diff, "rising": rising, "new_related": new_related,
            "new_related_note": note}


# ── Markdown 보고서 ────────────────────────────────────────────────
def fmt_total(e: dict) -> str:
    """'< 10' 때문에 합계가 10 미만이면 '<10', 아니면 천 단위 구분."""
    t = e.get("total", 0)
    return "<10" if e.get("has_lt10") and t < 10 else f"{t:,}"


def fmt_signed(n: int | None) -> str:
    return "—" if n is None else "0" if n == 0 else f"{n:+,}"


def fmt_pct(p: float) -> str:
    return ">+999%" if p > 999 else f"{p:+,.0f}%"


def md_date(iso: str | None) -> str:
    """'2026-09-29' → '9/29' (없으면 '-')."""
    if not iso:
        return "-"
    d = date.fromisoformat(iso)
    return f"{d.month}/{d.day}"


def cell(s) -> str:
    return str("—" if s is None else s).replace("|", "\\|")


def name_list(names: list[str]) -> str:
    """앞 FAILED_SHOW개 + '외 N개'."""
    more = f" 외 {len(names) - FAILED_SHOW}개" if len(names) > FAILED_SHOW else ""
    return ", ".join(names[:FAILED_SHOW]) + more


def render_md(snap: dict, diffs: dict, days: int) -> str:
    no_data, failed = snap["no_data_seeds"], snap["failed_seeds"]
    cmp = ([f"전일 {md_date(diffs['prev_date'])}"] if diffs["prev_date"] else []) \
        + ([f"7일 {md_date(diffs['week_date'])}"] if diffs["week_date"] else [])
    L = [f"# TCG 검색 수요 — {snap['date']}",
         f"상태: {'부분' if no_data else '정상'} {len(snap['seeds'])}/{snap['seed_count']}"
         + (" · 비교 " + " · ".join(cmp) if cmp else ""),
         f"수집 {snap['collected_at_kst']} KST · 네이버 검색광고 API"]
    if no_data:
        L.append(f"> {WARN} 데이터 없음 {len(no_data)}개: {name_list(no_data)}"
                 + (f" (요청 실패 {len(failed)}개 포함)" if failed else ""))
    L.append("")

    # 1) 급상승
    L.append(f"## 🔥 급상승 (7일 전 대비, 월간 검색량 {RISING_MIN_TOTAL} 이상)")
    if diffs["week_date"] is None:
        L.append(f"8일째부터 표시돼요 (지금 {days}일째)" if days < 8
                 else "7~10일 전 기록이 없어 비교를 건너뛰어요")
    elif not diffs["rising"]:
        L.append(f"+{RISING_MIN_PCT:g}% 이상 오른 키워드가 없어요")
    else:
        L += [f"| 키워드 | 월간 | vs {md_date(diffs['week_date'])} |", "|---|---:|---:|"] + [
            f"| {cell(r['keyword'])} | {r['total']:,} | "
            + ("신규 |" if r["new"] else f"{fmt_pct(r['week_pct'])} ({fmt_signed(r['week_abs'])}) |")
            for r in diffs["rising"][:TOP_N]]
        if len(diffs["rising"]) > TOP_N:
            L.append(f"외 {len(diffs['rising']) - TOP_N}개는 latest.json 참고")
    L.append("")

    # 2) 새 연관 검색어
    L.append(f"## 🆕 새 연관 검색어 (최근 7일 없던 것, 월간 검색량 {NEW_REL_MIN_TOTAL} 이상)")
    nr = diffs["new_related"]
    if diffs["new_related_note"]:
        L.append(diffs["new_related_note"])
    elif not nr:
        L.append("새로 잡힌 연관 검색어가 없어요")
    else:
        L += ["| 키워드 | 월간 | 광고경쟁 |", "|---|---:|:---:|"] + [
            f"| {cell(r['keyword'])} | {fmt_total(r)} | {cell(r['compIdx'])} |" for r in nr[:TOP_N]]
        if len(nr) > TOP_N:
            L.append(f"외 {len(nr) - TOP_N}개는 latest.json 참고")
    L.append("")

    # 3) 내 키워드: 전일 대비 변화(절댓값) 큰 순
    L.append("## 📊 내 키워드 (전일 대비 변화 큰 순)")
    ds = diffs["seeds"]
    mine = sorted(snap["seeds"].items(),
                  key=lambda kv: (-abs(ds[kv[0]]["day_abs"] or 0), -kv[1]["total"]))
    col = f"vs {md_date(diffs['prev_date'])}" if diffs["prev_date"] else "전일 대비"
    L += [f"| 키워드 | 월간 | {col} |", "|---|---:|---:|"] + [
        f"| {cell(kw)} | {fmt_total(e)} | {fmt_signed(ds[kw]['day_abs'])} |"
        for kw, e in mine[:TOP_N]]
    if len(mine) > TOP_N:
        L.append(f"나머지 {len(mine) - TOP_N}개는 latest.json 참고")
    L.append("")

    # 4) 연관 검색어 TOP
    L.append(f"## 🔎 연관 검색어 TOP {TOP_N} (필터 통과)")
    rel = sorted(snap["related"].items(), key=lambda kv: -kv[1]["total"])[:TOP_N]
    if rel:
        L += ["| 키워드 | 월간 | 광고경쟁 |", "|---|---:|:---:|"] + [
            f"| {cell(kw)} | {fmt_total(e)} | {cell(e.get('compIdx'))} |" for kw, e in rel]
    else:
        L.append("필터를 통과한 연관 검색어가 없어요")
    L += ["", FOOTNOTE, ""]
    return "\n".join(L)


# ── 실행 흐름 ───────────────────────────────────────────────────────
def get_today(now_kst: datetime) -> date:
    """KST 기준 오늘. COLLECT_TODAY(테스트용)가 있으면 그 날짜."""
    override = os.environ.get("COLLECT_TODAY", "").strip()
    return date.fromisoformat(override) if override else now_kst.date()


def build_outputs(result: dict, seeds: list[str], today: date, now: datetime, data_dir: Path):
    """스냅샷·비교·보고서를 만들어 저장한다."""
    hist_dir = data_dir / "history"
    history = [h for h in list_history(hist_dir) if h[0] != today]  # 같은 날 재실행은 비교 제외
    prev_ref, week_ref = pick_baselines(history, today)
    prev = load_json(prev_ref[1]) if prev_ref else None
    week = load_json(week_ref[1]) if week_ref else None
    w_lo = today - timedelta(days=NEW_REL_WINDOW)
    window = [s for s in (load_json(p) for d, p in history if w_lo <= d < today) if s]

    today_keys = {norm(k) for k in result["seeds"]}
    full = result["related"]
    no_data = [s for s in seeds if s not in result["seeds"]]
    snap = {
        "schema_version": SCHEMA_VERSION,
        "date": today.isoformat(),
        "collected_at": now.isoformat(timespec="seconds"),
        "collected_at_kst": now.strftime("%Y-%m-%d %H:%M"),
        "status": "partial" if no_data else "ok",
        "seed_count": len(seeds),
        "batches": result["batches"],
        "ok_batches": result["ok_batches"],
        "failed_seeds": result["failed_seeds"],
        "no_data_seeds": no_data,
        # 이전 스냅샷에는 있었는데 오늘은 값이 없는 seed (실패·응답 누락·목록에서 삭제 포함)
        "missing_seeds": [k for k in (prev or {}).get("seeds", {}) if norm(k) not in today_keys],
        "seeds": result["seeds"],
        "related": dict(sorted(full.items(), key=lambda kv: -kv[1]["total"])[:RELATED_KEEP]),
        "related_keys": sorted(full),
    }
    diffs = compute_diffs(snap, prev, week, window, full)
    days = sum(1 for d, _ in history if d < today) + 1  # 오늘 포함 누적 일수

    write_json(hist_dir / f"{today.isoformat()}.json", snap)
    write_json(data_dir / "latest.json", dict(snap, diffs=diffs, history_days=days))
    write_atomic(data_dir / "latest.md", render_md(snap, diffs, days))
    write_status(data_dir, today, snap["status"], f"데이터 없음 {len(no_data)}개" if no_data else "", now)
    return diffs, days, prune_history(hist_dir, today)


def already_ok(data_dir: Path, today: date) -> bool:
    """status.json이 오늘 날짜의 'ok'이면 True (부분 성공/실패면 다시 수집)."""
    st = load_json(data_dir / "status.json") if (data_dir / "status.json").is_file() else None
    return bool(st) and st.get("date") == today.isoformat() and st.get("status") == "ok"


def fail(today: date, now: datetime, reason: str) -> int:
    """실패 안내를 latest.md/status.json에 남기고 1을 반환 (워크플로가 커밋함).
    단, 오늘 이미 저장된 결과(예: 07:30 부분 성공)가 있으면 그 결과를 유지한다."""
    log(f"오류: {reason}")
    if (DATA_DIR / "history" / f"{today}.json").is_file():
        log("오늘 이미 저장된 결과가 있어 그대로 둡니다.")
    else:
        write_failure(DATA_DIR, today, reason, now)
    return 1


def run(today: date, now: datetime) -> int:
    missing = [k for k in REQUIRED_ENV if not os.environ.get(k, "").strip()]
    if missing:
        log("GitHub 저장소 Settings → Secrets and variables → Actions 에 등록했는지 확인하세요.")
        return fail(today, now, "필수 환경 변수 없음: " + ", ".join(missing))
    creds = {k: os.environ[k].strip() for k in REQUIRED_ENV}
    api_base = os.environ.get("NAVER_API_BASE", "").strip() or DEFAULT_API_BASE
    try:
        backoff_base = float(os.environ.get("COLLECT_BACKOFF_BASE") or 1.0)
    except ValueError:
        backoff_base = 1.0

    if not KEYWORDS_FILE.is_file():
        return fail(today, now, "keywords.txt 없음")
    seeds, filters, excludes = parse_keywords(KEYWORDS_FILE.read_text(encoding="utf-8-sig"))
    if not seeds:
        return fail(today, now, "keywords.txt에 키워드 없음")
    log(f"수집 시작: {today} (KST) · 키워드 {len(seeds)}개 · 필터 {len(filters)}개 · 제외 {len(excludes)}개")

    try:
        result = collect(seeds, filters, excludes, creds, api_base, backoff_base)
    except AuthError as e:
        return fail(today, now, str(e))
    if result["ok_batches"] == 0:
        return fail(today, now, "모든 요청 실패: " + "; ".join(dict.fromkeys(result["errors"]))[:150])

    diffs, days, pruned = build_outputs(result, seeds, today, now, DATA_DIR)
    log(f"완료: seed {len(result['seeds'])}/{len(seeds)}개, 연관 {len(result['related'])}개, "
        f"실패 {len(result['failed_seeds'])}개, 요청 {result['ok_batches']}/{result['batches']} 성공")
    log(f"비교: 전일={diffs['prev_date'] or '없음'}, 7일={diffs['week_date'] or '없음'}, "
        f"급상승 {len(diffs['rising'])}개, 새 연관 {len(diffs['new_related'])}개, 누적 {days}일째"
        + (f", 오래된 기록 {pruned}개 삭제" if pruned else ""))
    return 0


def main(argv: list[str]) -> int:
    now = datetime.now(KST)
    try:
        today = get_today(now)
    except ValueError:
        log("오류: COLLECT_TODAY 형식이 잘못됐습니다 (YYYY-MM-DD).")
        return 1
    if "--skip-if-done" in argv and already_ok(DATA_DIR, today):
        log(f"오늘({today}) 수집이 이미 정상 완료되어 건너뜁니다.")
        return 0
    try:
        return run(today, now)
    except Exception as e:  # 예외 메시지에는 비밀 정보가 섞일 수 있어 종류와 줄 번호만 남긴다
        frames = [f for f in traceback.extract_tb(e.__traceback__) if f.filename == __file__]
        line = frames[-1].lineno if frames else "?"  # collect.py 안에서 난 마지막 위치
        try:
            return fail(today, now, f"예기치 못한 오류: {type(e).__name__} (line {line})")
        except Exception:
            log("오류: 실패 안내 저장 중 다시 오류가 났습니다.")
            return 1


# ── 자체 점검 (--selftest): 네트워크 없이 핵심 로직 확인 ────────────────────────
def selftest() -> int:
    global fetch_batch, REQUEST_INTERVAL
    failures: list[str] = []

    def check(name: str, cond: bool) -> None:
        print(("  ok   " if cond else "  FAIL ") + name)
        if not cond:
            failures.append(name)

    # 1) 서명 — openssl로 별도 계산한 값:
    #    printf '1700000000000.GET./keywordstool' | openssl dgst -sha256 -hmac 'test-secret' -binary | base64
    check("signature vector", sign("1700000000000", "GET", "/keywordstool", "test-secret")
          == "pLnZJtUUxfdXitHXWo/EvKzookF5hlb/Rs2Fuw1W4js=")

    # 2) 값 파싱 / 표시 형식
    check("parse counts", parse_count(1234) == (1234, False) and parse_count("< 10") == (0, True)
          and parse_count("<10") == (0, True) and parse_count("1,234") == (1234, False)
          and parse_count(None) == (0, False))
    e = make_entry({"monthlyPcQcCnt": "< 10", "monthlyMobileQcCnt": 40, "compIdx": "낮음"})
    check("entry flags", e["total"] == 40 and e["has_lt10"] and e.get("pc_lt10")
          and "mobile_lt10" not in e and "monthlyPcQcCnt" not in e)
    check("fmt total", fmt_total({"total": 0, "has_lt10": True}) == "<10"
          and fmt_total({"total": 12345}) == "12,345")
    check("fmt signed", fmt_signed(1200) == "+1,200" and fmt_signed(-5) == "-5"
          and fmt_signed(None) == "—" and fmt_signed(0) == "0")
    check("fmt pct", fmt_pct(50.0) == "+50%" and fmt_pct(-12.6) == "-13%"
          and fmt_pct(1500) == ">+999%" and fmt_pct(999) == "+999%")

    # 3) keywords.txt 파싱 / 필터
    seeds, filters, excludes = parse_keywords(
        "# c\n\n포켓몬 카드\n포켓몬카드\nPSA10\npsa10\n[filter]\n포켓몬\nTCG\n카드\n[exclude]\n신한 카드\n뮤지컬\n")
    check("parse sections", seeds == ["포켓몬카드", "PSA10"] and filters == ["포켓몬", "tcg", "카드"]
          and excludes == ["신한카드", "뮤지컬"])
    check("relevance", is_relevant("포켓몬 카드 박스", filters, excludes)
          and is_relevant("Tcg샵", filters, excludes)
          and not is_relevant("신한 카드 혜택", filters, excludes)
          and not is_relevant("포켓몬 뮤지컬", filters, excludes)
          and not is_relevant("원신", filters, excludes) and is_relevant("x", [], []))

    # 4) collect: 400 분할 재조회, 다른 묶음에서 값을 얻은 seed는 실패 목록에서 제외
    def fake_fetch(batch, *a):
        if "BAD" in batch:
            raise BadRequest("HTTP 400 code=11001")
        if "FAIL" in batch:
            raise BatchError("HTTP 500")
        return [{"relKeyword": k, "monthlyPcQcCnt": 50, "monthlyMobileQcCnt": 60} for k in batch] \
            + [{"relKeyword": "F2", "monthlyPcQcCnt": 1, "monthlyMobileQcCnt": 2},
               {"relKeyword": "포켓몬 빵", "monthlyPcQcCnt": 5, "monthlyMobileQcCnt": 5},
               {"relKeyword": "신한카드", "monthlyPcQcCnt": 5, "monthlyMobileQcCnt": 5}]
    real_fetch, real_interval = fetch_batch, REQUEST_INTERVAL
    fetch_batch, REQUEST_INTERVAL = fake_fetch, 0
    try:
        r = collect(["A", "BAD", "C", "D", "E", "FAIL", "F2"], ["포켓몬"], ["신한카드"], {}, "", 0)
    finally:
        fetch_batch, REQUEST_INTERVAL = real_fetch, real_interval
    check("400 split", set(r["seeds"]) == {"A", "C", "D", "E", "F2"} and r["batches"] == 7
          and r["ok_batches"] == 4)
    check("failed cleanup", r["failed_seeds"] == ["BAD", "FAIL"])
    check("related filter", list(r["related"]) == ["포켓몬빵"])

    # 5) 기준 선택 / 비교 / 보고서 / 실패 안내 (임시 폴더)
    def snap(d, seeds, related=None, no_data=(), **extra):
        mk = lambda t: {"pc": t, "mobile": 0, "total": t, "has_lt10": False, "compIdx": "중간"}
        return dict({"date": d, "seeds": {k: mk(v) for k, v in seeds.items()},
                     "related": {k: mk(v) for k, v in (related or {}).items()},
                     "failed_seeds": [], "no_data_seeds": list(no_data),
                     "seed_count": len(seeds) + len(no_data), "collected_at_kst": f"{d} 07:31"}, **extra)

    with tempfile.TemporaryDirectory() as tmp:
        data = Path(tmp)
        hist = data / "history"
        hist.mkdir()
        for s in [snap("2025-08-01", {"A": 1}), snap("2026-08-01", {"A": 1}),
                  snap("2026-09-18", {"A": 1}),                       # 12일 전 → 7일 기준 아님
                  snap("2026-09-22", {"A": 100, "B": 200, "Z": 0}),   # 8일 전 → 7일 기준
                  snap("2026-09-25", {"A": 1, "OLD SEED": 5}, {"seen5": 500}),  # related_keys 없는 옛 형식
                  snap("2026-09-29", {"A": 110, "B": 300}, {"old": 150}, related_keys=["old", "hidden"])]:
            (hist / f"{s['date']}.json").write_text(json.dumps(s, ensure_ascii=False), encoding="utf-8")
        (hist / "notes.json").write_text("{}", encoding="utf-8")
        today = date(2026, 9, 30)
        hl = list_history(hist)
        prev_ref, week_ref = pick_baselines(hl, today)
        check("baselines", prev_ref[0] == date(2026, 9, 29) and week_ref[0] == date(2026, 9, 22))
        check("week window", pick_baselines(hl[:3], date(2026, 9, 30))[1] is None)

        window = [load_json(p) for d, p in hl if date(2026, 9, 23) <= d < today]
        rel = {"old": 160, "seen5": 700, "new1": 140, "small": 99, "NEW 3": 999}
        cur = snap("2026-09-30", {"A": 150, "B": 230, "C": 500, "Z": 120}, rel)
        full = snap("x", {}, dict(rel, hidden=300, oldseed=400, cutoff=120))["related"]  # 500개 컷 밖 포함
        dif = compute_diffs(cur, load_json(prev_ref[1]), load_json(week_ref[1]), window, full)
        check("day/week diff", dif["seeds"]["A"]["day_abs"] == 40 and dif["seeds"]["B"]["day_abs"] == -70
              and dif["seeds"]["A"]["week_pct"] == 50.0 and dif["seeds"]["C"]["day_abs"] is None)
        check("rising (new first)", [(r["keyword"], r["new"]) for r in dif["rising"]]
              == [("Z", True), ("A", False)])
        check("new related (full set, keys+seeds union)",
              [r["keyword"] for r in dif["new_related"]] == ["NEW 3", "new1", "cutoff"])
        dif_f = compute_diffs(cur, None, None, window[:-1] + [dict(snap("2026-09-29", {}), failed_seeds=["X"])])
        check("new related note", dif_f["new_related"] == [] and "일부 실패" in dif_f["new_related_note"])
        dif0 = compute_diffs(cur, None, None, [])
        check("no baseline", dif0["rising"] == [] and "기록이 없어" in dif0["new_related_note"])

        md0 = render_md(cur, dif0, 1)
        check("md placeholder", "8일째부터 표시돼요 (지금 1일째)" in md0 and "| 키워드 | 월간 | 전일 대비 |" in md0
              and md0.splitlines()[1] == "상태: 정상 4/4")
        big = snap("2026-09-30", {f"키워드{i:02d}": i * 37 for i in range(38)},
                   {f"연관검색어{i:03d}": i for i in range(500)}, [f"없음{i}" for i in range(7)])
        big["failed_seeds"] = ["없음0", "없음1"]
        md = render_md(big, compute_diffs(big, big, big, [big]), 9)
        check("md size/status", len(md.splitlines()) <= 65 and len(md.encode()) < 4096
              and md.splitlines()[1] == "상태: 부분 38/45 · 비교 전일 9/30 · 7일 9/30"
              and "데이터 없음 7개: 없음0, 없음1, 없음2, 없음3, 없음4 외 2개 (요청 실패 2개 포함)" in md
              and "나머지 28개는 latest.json 참고" in md and FOOTNOTE in md)
        md1 = render_md(cur, dif, 9)
        check("md rows", "| Z | 120 | 신규 |" in md1 and "| A | 150 | +50% (+50) |" in md1
              and "| 키워드 | 월간 | vs 9/29 |" in md1 and md1.splitlines()[1].endswith("비교 전일 9/29 · 7일 9/22"))
        check("rising overflow", "외 2개는 latest.json 참고" in render_md(cur, dict(dif, rising=dif["rising"] * 6), 9))

        write_atomic(data / "latest.md", md1)
        write_json(data / "latest.json", {"date": "2026-09-30"})
        before = (data / "latest.json").read_bytes()
        now = datetime(2026, 10, 1, 7, 30, tzinfo=KST)
        write_failure(data, date(2026, 10, 1), "HTTP 500", now)
        write_failure(data, date(2026, 10, 2), "HTTP 401", now)  # 이전 안내는 교체되어야 함
        out = (data / "latest.md").read_text(encoding="utf-8").splitlines()
        check("failure notice", out[0] == f"{FAIL_MARK} 오늘(2026-10-02) 수집 실패 (HTTP 401) — 아래는 2026-09-30 데이터"
              and out[2] == md1.splitlines()[0] and out[3] == "상태: 실패 — 아래는 9/30 데이터"
              and sum(line.startswith(FAIL_MARK) for line in out) == 1
              and (data / "latest.json").read_bytes() == before
              and load_json(data / "status.json")["status"] == "failed")
        d1 = date(2026, 10, 2)
        ok_now = not already_ok(data, d1)
        write_status(data, d1, "partial", "", now)
        ok_now = ok_now and not already_ok(data, d1)
        write_status(data, d1, "ok", "", now)
        check("skip-if-done", ok_now and already_ok(data, d1) and not already_ok(data, date(2026, 10, 3)))

        bom = data / "bom.txt"
        bom.write_bytes("\ufeff포켓몬카드\n".encode("utf-8"))
        check("BOM", parse_keywords(bom.read_text(encoding="utf-8-sig"))[0] == ["포켓몬카드"])
        check("prune", prune_history(hist, today) == 1 and not (hist / "2025-08-01.json").exists())
        write_atomic(data / "o" / "x.md", "a")
        write_atomic(data / "o" / "x.md", "b")
        check("atomic write", (data / "o" / "x.md").read_text() == "b"
              and [p.name for p in (data / "o").iterdir()] == ["x.md"])

    print("PASS" if not failures else f"FAIL ({len(failures)}): " + ", ".join(failures))
    return 0 if not failures else 1


if __name__ == "__main__":
    if "--selftest" in sys.argv[1:]:
        sys.exit(selftest())
    sys.exit(main(sys.argv[1:]))
