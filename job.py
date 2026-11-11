"""
Smart Money Radar - congress job.

Runs every hour on GitHub Actions. It:
  1. asks your Worker which filings it already has,
  2. reads new House trade reports (PDFs listed in the Clerk's yearly index),
  3. reads new Senate trade reports (web pages on efdsearch.senate.gov),
  4. sends the trades to your Worker.

Settings (GitHub repo -> Settings -> Secrets and variables -> Actions):
  RADAR_URL    e.g. https://smart-money-radar.yourname.workers.dev
  INGEST_KEY   the same secret text you set on the Worker
  SEC_CONTACT  "Your Name you@email.com" (sent as the User-Agent)
"""
import io
import json
import os
import re
import sys
import time
import zipfile
import xml.etree.ElementTree as ET
from datetime import date, datetime, timedelta

import requests

LOOKBACK_DAYS = int(os.environ.get("LOOKBACK_DAYS", "120"))
MAX_HOUSE = int(os.environ.get("MAX_HOUSE", "80"))
MAX_SENATE = int(os.environ.get("MAX_SENATE", "80"))
UA = os.environ.get("SEC_CONTACT", "SmartMoneyRadar research bot")

HOUSE_INDEX = "https://disclosures-clerk.house.gov/public_disc/financial-pdfs/{year}FD.zip"
HOUSE_PDF = "https://disclosures-clerk.house.gov/public_disc/ptr-pdfs/{year}/{doc}.pdf"
SENATE = "https://efdsearch.senate.gov"
LEGISLATORS = "https://unitedstates.github.io/congress-legislators/legislators-current.json"

AMOUNT_RE = re.compile(r"(Over\s+\$[\d,]+|\$[\d,]+\s*-\s*\$[\d,]+|\$[\d,]+)")


def log(*a):
    print(*a, flush=True)


# ---------------------------------------------------------------- helpers

def parse_amount(text):
    """'$1,001 - $15,000' -> (1001, 15000, label); 'Over $50,000,000' -> (50000001, None, label)."""
    if not text:
        return None, None, ""
    t = " ".join(text.split())
    m = AMOUNT_RE.search(t)
    if not m:
        return None, None, t
    label = m.group(1)
    nums = [int(x.replace(",", "")) for x in re.findall(r"\$([\d,]+)", label)]
    if label.lower().startswith("over"):
        return nums[0] + 1, None, label
    if len(nums) == 2:
        return nums[0], nums[1], label
    return nums[0], nums[0], label


def side_of(t):
    t = (t or "").strip().lower()
    if t.startswith("p"):
        return "buy"
    if t.startswith("s"):
        return "sell"
    if t.startswith("e"):
        return "exchange"
    return ""


def owner_of(code):
    c = (code or "").strip().upper()
    return {"SP": "Spouse", "SPOUSE": "Spouse", "JT": "Joint", "JOINT": "Joint", "DC": "Child", "CHILD": "Child",
            "DEPENDENT CHILD": "Child"}.get(c, "Self")


def iso(d):
    """Accepts M/D/YYYY or YYYY-MM-DD."""
    d = (d or "").strip()
    for fmt in ("%m/%d/%Y", "%Y-%m-%d"):
        try:
            return datetime.strptime(d, fmt).date().isoformat()
        except ValueError:
            pass
    return ""


class Legislators:
    """Adds party and state, e.g. 'Nancy Pelosi (D-CA)'."""

    def __init__(self, session):
        self.rows = []
        try:
            data = session.get(LEGISLATORS, timeout=30).json()
            for p in data:
                term = p["terms"][-1]
                n = p["name"]
                self.rows.append({
                    "last": n.get("last", "").lower(),
                    "first": n.get("first", "").lower(),
                    "nick": (n.get("nickname") or "").lower(),
                    "official": n.get("official_full") or f"{n.get('first')} {n.get('last')}",
                    "chamber": "House" if term["type"] == "rep" else "Senate",
                    "party": (term.get("party") or "")[:1],
                    "state": term.get("state", ""),
                })
        except Exception as e:  # enrichment is optional
            log("legislator list unavailable:", e)

    def find(self, first, last, chamber, state=None):
        last_l = (last or "").lower().strip()
        first_l = (first or "").lower().strip()
        cands = [r for r in self.rows if r["chamber"] == chamber and (r["last"] == last_l or last_l.endswith(r["last"]) or r["last"].endswith(last_l))]
        if state:
            cands = [r for r in cands if r["state"] == state] or cands
        if len(cands) > 1 and first_l:
            f = [r for r in cands if first_l[:3] in (r["first"][:3], r["nick"][:3])]
            cands = f or cands
        return cands[0] if len(cands) == 1 else None


# ---------------------------------------------------------------- House

HOUSE_JUNK = re.compile(r"^\s*(F\s*S|S\s*O|D|C|L|Filing ID|Filing Status|Subholding Of|Description|Comments|Location|\*)\s*[:#]", re.I)
HOUSE_DATE = re.compile(r"^\d{1,2}/\d{1,2}/\d{4}$")
HOUSE_TICKER = re.compile(r"\(([A-Z][A-Z0-9.\-]{0,6})\)")
HOUSE_ASSET_TYPE = re.compile(r"\[([A-Z]{2,3})\]")


def house_rows_from_words(words):
    """Table reader: uses the column header positions to place each word in a column.
    words: pdfplumber word dicts for one page (x0, top, text)."""
    hdr = {}
    for w in words:
        t = w["text"]
        if t == "Owner" and "owner" not in hdr:
            hdr["owner"] = w
        elif t == "Asset" and "asset" not in hdr:
            hdr["asset"] = w
        elif t == "Transaction" and "type" not in hdr:
            hdr["type"] = w
        elif t == "Notification" and "notif" not in hdr:
            hdr["notif"] = w
        elif t == "Amount" and "amount" not in hdr:
            hdr["amount"] = w
        elif t in ("Cap.", "Cap") and "cap" not in hdr:
            hdr["cap"] = w
    if not all(k in hdr for k in ("owner", "asset", "type", "notif", "amount")):
        return None
    head_y = max(h["top"] for h in hdr.values())
    # the trade "Date" column sits between Transaction Type and Notification Date
    date_hdr = [w for w in words if w["text"] == "Date" and hdr["type"]["x0"] < w["x0"] < hdr["notif"]["x0"]]
    x_owner = hdr["owner"]["x0"] - 3
    x_asset = hdr["asset"]["x0"] - 3
    x_type = hdr["type"]["x0"] - 3
    x_date = (min(w["x0"] for w in date_hdr) if date_hdr else hdr["type"]["x0"] + 45) - 3
    x_notif = hdr["notif"]["x0"] - 3
    x_amount = hdr["amount"]["x0"] - 3
    x_cap = hdr["cap"]["x0"] - 3 if "cap" in hdr else 10_000

    def col(w):
        x = w["x0"]
        if x < x_owner:
            return "id"
        if x < x_asset:
            return "owner"
        if x < x_type:
            return "asset"
        if x < x_date:
            return "type"
        if x < x_notif:
            return "date"
        if x < x_amount:
            return "notif"
        if x < x_cap:
            return "amount"
        return "cap"

    body = sorted([w for w in words if w["top"] > head_y + 4], key=lambda w: (round(w["top"]), w["x0"]))
    anchors = sorted({round(w["top"]) for w in body if col(w) == "date" and HOUSE_DATE.match(w["text"])})
    rows = []
    for i, y in enumerate(anchors):
        y_end = anchors[i + 1] - 2 if i + 1 < len(anchors) else 10_000
        # a wrapped row can start a hair above its date; include 3pt above
        seg = [w for w in body if y - 3 <= round(w["top"]) < y_end]
        lines = {}
        for w in seg:
            lines.setdefault(round(w["top"]), []).append(w)
        cells = {k: [] for k in ("owner", "asset", "type", "date", "notif", "amount")}
        stop_asset = False
        for top in sorted(lines):
            lw = sorted(lines[top], key=lambda w: w["x0"])
            asset_text = " ".join(w["text"] for w in lw if col(w) == "asset")
            if HOUSE_JUNK.match(asset_text) or HOUSE_JUNK.match(" ".join(w["text"] for w in lw)):
                stop_asset = True
            for w in lw:
                c = col(w)
                if c == "asset" and stop_asset:
                    continue
                if c in cells:
                    cells[c].append(w["text"])
        rows.append({k: " ".join(v) for k, v in cells.items()})
    return rows


def house_rows_from_text(text):
    """Fallback reader for when the column header can't be found: works on the plain text."""
    keep = []
    for line in text.replace("\x00", "").splitlines():
        if HOUSE_JUNK.match(line):
            continue
        keep.append(line.strip())
    flat = " ".join(keep)
    pat = re.compile(
        r"(?:\b(SP|JT|DC)\s+)?([^\[\]]{2,160}?\[[A-Z]{2,3}\])\s*(P|S\s*\(partial\)|S|E)\s+"
        r"(\d{1,2}/\d{1,2}/\d{4})\s+(\d{1,2}/\d{1,2}/\d{4})\s+(Over\s+\$[\d,]+|\$[\d,]+\s*-\s*\$[\d,]+)"
    )
    rows = []
    for m in pat.finditer(flat):
        rows.append({"owner": m.group(1) or "", "asset": m.group(2), "type": m.group(3), "date": m.group(4),
                     "notif": m.group(5), "amount": m.group(6)})
    if rows:
        return rows
    # wrapped layout: the second half of the asset name and the [type] land after the first half of the amount
    pat2 = re.compile(
        r"(?:\b(SP|JT|DC)\s+)?(.{2,160}?)\s+(P|S\s*\(partial\)|S|E)\s+(\d{1,2}/\d{1,2}/\d{4})\s+(\d{1,2}/\d{1,2}/\d{4})\s+"
        r"(\$[\d,]+)\s*-\s*(.{0,80}?\[[A-Z]{2,3}\])\s*(\$[\d,]+)"
    )
    for m in pat2.finditer(flat):
        rows.append({"owner": m.group(1) or "", "asset": m.group(2) + " " + m.group(7), "type": m.group(3), "date": m.group(4),
                     "notif": m.group(5), "amount": f"{m.group(6)} - {m.group(8)}"})
    return rows


def clean_house_row(r):
    asset = " ".join((r.get("asset") or "").split())
    # drop table header debris that sometimes leaks in
    asset = re.sub(r"^.*\$200\?\s*", "", asset)
    owner_code = (r.get("owner") or "").split()[0] if r.get("owner") else ""
    m_own = re.match(r"^(SP|JT|DC)\s+", asset)
    if m_own and not owner_code:
        owner_code, asset = m_own.group(1), asset[m_own.end():]
    tick = HOUSE_TICKER.search(asset)
    atype = HOUSE_ASSET_TYPE.search(asset)
    t = (r.get("type") or "").strip()
    amt_min, amt_max, label = parse_amount(r.get("amount"))
    return {
        "owner": owner_of(owner_code),
        "asset": re.sub(r"\s*\[[A-Z]{2,3}\]\s*", " ", asset).strip(),
        "ticker": tick.group(1) if tick else None,
        "asset_type": atype.group(1) if atype else "",
        "side": side_of(t),
        "partial": "partial" in t.lower(),
        "trade_date": iso((r.get("date") or "").split()[0] if r.get("date") else ""),
        "amount_min": amt_min, "amount_max": amt_max, "amount_label": label,
    }


def parse_house_pdf(data):
    """Returns (rows, status). status: ok | scanned | unreadable"""
    import pdfplumber
    rows, text_all = [], []
    with pdfplumber.open(io.BytesIO(data)) as pdf:
        for page in pdf.pages:
            words = page.extract_words(keep_blank_chars=False, use_text_flow=False, x_tolerance=1.5, y_tolerance=2)
            for w in words:
                w["text"] = w["text"].replace("\x00", "")
            text_all.append(page.extract_text() or "")
            got = house_rows_from_words(words)
            if got:
                rows.extend(got)
    text = "\n".join(text_all).replace("\x00", "")
    if len(text.strip()) < 40:
        return [], "scanned"
    if not rows:
        rows = house_rows_from_text(text)
    cleaned = [clean_house_row(r) for r in rows]
    cleaned = [r for r in cleaned if r["side"] and r["trade_date"]]
    return cleaned, ("ok" if cleaned else "unreadable")


def house_filings(session, since):
    out = []
    years = sorted({since.year, date.today().year})
    for y in years:
        r = session.get(HOUSE_INDEX.format(year=y), timeout=60)
        if r.status_code != 200:
            log(f"House index {y}: HTTP {r.status_code}")
            continue
        z = zipfile.ZipFile(io.BytesIO(r.content))
        name = next(n for n in z.namelist() if n.lower().endswith(".xml"))
        root = ET.fromstring(z.read(name))
        for m in root.iter("Member"):
            g = lambda k: (m.findtext(k) or "").strip()
            if g("FilingType") != "P":
                continue
            filed = iso(g("FilingDate"))
            if not filed or filed < since.isoformat():
                continue
            st = g("StateDst")
            out.append({
                "id": "H-" + g("DocID"), "doc": g("DocID"), "year": g("Year") or str(y),
                "first": g("First"), "last": g("Last"), "state": st[:2] if re.match(r"^[A-Z]{2}", st) else "",
                "district": st[2:], "filed_at": filed,
            })
    out.sort(key=lambda f: f["filed_at"], reverse=True)
    return out


# ---------------------------------------------------------------- Senate

def senate_session(session):
    """Passes the eFD 'I agree' gate and returns the CSRF token for searches."""
    r = session.get(f"{SENATE}/search/home/", timeout=30)
    r.raise_for_status()
    m = re.search(r'name="csrfmiddlewaretoken"\s+value="([^"]+)"', r.text)
    if not m:
        raise RuntimeError("Senate: agreement form not found")
    r = session.post(f"{SENATE}/search/home/", data={"prohibition_agreement": "1", "csrfmiddlewaretoken": m.group(1)},
                     headers={"Referer": f"{SENATE}/search/home/"}, timeout=30)
    r.raise_for_status()
    return session.cookies.get("csrftoken") or m.group(1)


def senate_filings(session, since):
    token = senate_session(session)
    out, start = [], 0
    while True:
        r = session.post(f"{SENATE}/search/report/data/", data={
            "start": str(start), "length": "100", "report_types": "[11]", "filer_types": "[]",
            "submitted_start_date": since.strftime("%m/%d/%Y") + " 00:00:00", "submitted_end_date": "",
            "candidate_state": "", "senator_state": "", "office_id": "", "first_name": "", "last_name": "",
            "csrfmiddlewaretoken": token,
        }, headers={"Referer": f"{SENATE}/search/", "X-CSRFToken": token}, timeout=30)
        r.raise_for_status()
        data = r.json().get("data", [])
        for row in data:
            first, last, _ftype, link_html, filed = (row + [""] * 5)[:5]
            m = re.search(r'href="([^"]+)"', link_html)
            if not m:
                continue
            href = m.group(1)
            uid = href.rstrip("/").split("/")[-1]
            out.append({
                "id": "S-" + uid, "href": SENATE + href if href.startswith("/") else href,
                "paper": "/paper/" in href, "first": re.sub(r"<[^>]+>", "", first).strip(),
                "last": re.sub(r"<[^>]+>", "", last).strip(), "filed_at": iso(filed),
            })
        if len(data) < 100:
            break
        start += 100
        time.sleep(1)
    out.sort(key=lambda f: f["filed_at"], reverse=True)
    return out


def parse_senate_ptr(html):
    """Reads the transactions table on an electronic Senate PTR page."""
    from bs4 import BeautifulSoup
    soup = BeautifulSoup(html, "html.parser")
    table = None
    for t in soup.find_all("table"):
        heads = [th.get_text(" ", strip=True).lower() for th in t.find_all("th")]
        if any("transaction date" in h for h in heads) and any("amount" in h for h in heads):
            table = t
            break
    if not table:
        return []
    heads = [th.get_text(" ", strip=True).lower() for th in table.find("thead").find_all("th")] if table.find("thead") else \
            [th.get_text(" ", strip=True).lower() for th in table.find_all("th")]

    def idx(name):
        for i, h in enumerate(heads):
            if name in h:
                return i
        return None

    ix = {k: idx(k) for k in ("transaction date", "owner", "ticker", "asset name", "asset type", "type", "amount")}
    # "type" also matches "asset type": pick the type column that isn't asset type
    for i, h in enumerate(heads):
        if h.strip() == "type":
            ix["type"] = i
    rows = []
    body = table.find("tbody") or table
    for tr in body.find_all("tr"):
        tds = [td.get_text(" ", strip=True) for td in tr.find_all("td")]
        if len(tds) < 5:
            continue
        get = lambda k: tds[ix[k]] if ix.get(k) is not None and ix[k] < len(tds) else ""
        ticker = get("ticker").strip()
        ticker = None if ticker in ("", "--", "N/A") else re.sub(r"[^A-Z0-9.\-]", "", ticker.upper()) or None
        amt_min, amt_max, label = parse_amount(get("amount"))
        t = get("type")
        rows.append({
            "owner": owner_of(get("owner")), "asset": get("asset name"), "ticker": ticker,
            "asset_type": get("asset type"), "side": side_of(t), "partial": "partial" in t.lower(),
            "trade_date": iso(get("transaction date")),
            "amount_min": amt_min, "amount_max": amt_max, "amount_label": label,
        })
    return [r for r in rows if r["side"] and r["trade_date"]]


# ---------------------------------------------------------------- Worker

class Radar:
    def __init__(self, base, key):
        self.base = base.rstrip("/")
        self.h = {"Authorization": f"Bearer {key}", "Content-Type": "application/json", "User-Agent": "radar-congress-job"}

    def seen(self):
        r = requests.get(self.base + "/api/congress/seen", headers=self.h, timeout=60)
        r.raise_for_status()
        return set(r.json().get("ids", []))

    def send(self, filings, trades):
        for i in range(0, max(len(filings), 1), 40):
            fs = filings[i:i + 40]
            ids = {f["id"] for f in fs}
            ts = [t for t in trades if t["filing_id"] in ids]
            r = requests.post(self.base + "/api/congress/ingest", headers=self.h,
                              data=json.dumps({"filings": fs, "trades": ts}), timeout=60)
            if r.status_code != 200:
                raise RuntimeError(f"ingest failed {r.status_code}: {r.text[:300]}")


def member_fields(leg, first, last, chamber, state=None, district=""):
    hit = leg.find(first, last, chamber, state)
    name = hit["official"] if hit else f"{first} {last}".strip()
    party = hit["party"] if hit else ""
    st = state or (hit["state"] if hit else "")
    return {"member": name, "party": party, "state": st, "district": district}


def main():
    base, key = os.environ.get("RADAR_URL"), os.environ.get("INGEST_KEY")
    if not base or not key:
        sys.exit("Set RADAR_URL and INGEST_KEY")
    radar = Radar(base, key)
    s = requests.Session()
    s.headers["User-Agent"] = UA
    since = date.today() - timedelta(days=LOOKBACK_DAYS)
    seen = radar.seen()
    leg = Legislators(s)
    log(f"Worker already has {len(seen)} filings; looking back to {since}")
    summary = {}

    # ---- House
    try:
        hf = [f for f in house_filings(s, since) if f["id"] not in seen][:MAX_HOUSE]
        log(f"House: {len(hf)} new reports to read")
        filings, trades = [], []
        for f in hf:
            url = HOUSE_PDF.format(year=f["year"], doc=f["doc"])
            try:
                r = s.get(url, timeout=60)
                if r.status_code != 200:
                    log(f"  {f['id']} HTTP {r.status_code} (will retry next run)")
                    continue
                rows, status = parse_house_pdf(r.content)
            except Exception as e:
                rows, status = [], "error"
                log(f"  {f['id']} error: {e}")
            m = member_fields(leg, f["first"], f["last"], "House", f["state"], f["district"])
            filings.append({"id": f["id"], "chamber": "House", "filed_at": f["filed_at"], "url": url, "status": status, **m})
            for n, row in enumerate(rows):
                trades.append({"id": f"{f['id']}-{n}", "filing_id": f["id"], "chamber": "House", "filed_at": f["filed_at"], "url": url, **m, **row})
            log(f"  {f['id']} {m['member']}: {status}, {len(rows)} trades")
            time.sleep(1)
        radar.send(filings, trades)
        summary["house"] = {"reports": len(filings), "trades": len(trades)}
    except Exception as e:
        log("House step failed:", repr(e))
        summary["house_error"] = repr(e)

    # ---- Senate
    try:
        sf = [f for f in senate_filings(s, since) if f["id"] not in seen][:MAX_SENATE]
        log(f"Senate: {len(sf)} new reports to read")
        filings, trades = [], []
        for f in sf:
            m = member_fields(leg, f["first"], f["last"], "Senate")
            if f["paper"]:
                filings.append({"id": f["id"], "chamber": "Senate", "filed_at": f["filed_at"], "url": f["href"], "status": "scanned", **m})
                continue
            try:
                r = s.get(f["href"], timeout=60, headers={"Referer": f"{SENATE}/search/"})
                if r.status_code != 200 or "prohibition_agreement" in r.text:
                    log(f"  {f['id']} HTTP {r.status_code} (will retry next run)")
                    continue
                rows = parse_senate_ptr(r.text)
                status = "ok" if rows else "unreadable"
            except Exception as e:
                rows, status = [], "error"
                log(f"  {f['id']} error: {e}")
            filings.append({"id": f["id"], "chamber": "Senate", "filed_at": f["filed_at"], "url": f["href"], "status": status, **m})
            for n, row in enumerate(rows):
                trades.append({"id": f"{f['id']}-{n}", "filing_id": f["id"], "chamber": "Senate", "filed_at": f["filed_at"], "url": f["href"], **m, **row})
            log(f"  {f['id']} {m['member']}: {status}, {len(rows)} trades")
            time.sleep(1)
        radar.send(filings, trades)
        summary["senate"] = {"reports": len(filings), "trades": len(trades)}
    except Exception as e:
        log("Senate step failed:", repr(e))
        summary["senate_error"] = repr(e)

    log("Summary:", json.dumps(summary))
    if "house_error" in summary and "senate_error" in summary:
        sys.exit(1)


if __name__ == "__main__":
    main()
