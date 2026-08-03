#!/usr/bin/env python3
from __future__ import annotations

import csv
import datetime as dt
import html.parser
import json
import re
import urllib.parse
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DATA_DIR = ROOT / "data"
DATA_DIR.mkdir(parents=True, exist_ok=True)

FUNDS = {
    "distribution": {
        "page": "https://www.alamco.co.jp/fund/WCM_es/index.html",
        "filename": "171514_price.csv",
        "output": DATA_DIR / "wcm_distribution.csv",
    },
    "growth": {
        "page": "https://www.alamco.co.jp/fund/WCM_ag/index.html",
        "filename": "170514_price.csv",
        "output": DATA_DIR / "wcm_growth.csv",
    },
}

HEADERS = {
    "User-Agent": "Mozilla/5.0 (compatible; WCMAnalyzerDataUpdater/1.0)",
    "Accept": "text/html,text/csv,application/octet-stream;q=0.9,*/*;q=0.8",
}


class LinkParser(html.parser.HTMLParser):
    def __init__(self):
        super().__init__()
        self.links = []
        self.href = None
        self.text = []

    def handle_starttag(self, tag, attrs):
        if tag.lower() == "a":
            self.href = dict(attrs).get("href")
            self.text = []

    def handle_data(self, data):
        if self.href is not None:
            self.text.append(data)

    def handle_endtag(self, tag):
        if tag.lower() == "a" and self.href is not None:
            self.links.append((self.href, "".join(self.text).strip()))
            self.href = None
            self.text = []


def fetch(url):
    request = urllib.request.Request(url, headers=HEADERS)
    with urllib.request.urlopen(request, timeout=45) as response:
        return response.read(), response.geturl()


def decode_csv(data):
    for encoding in ("cp932", "shift_jis", "utf-8-sig", "utf-8"):
        try:
            return data.decode(encoding), encoding
        except UnicodeDecodeError:
            pass
    raise ValueError("Unsupported CSV encoding")


def looks_like_price_csv(data):
    if len(data) < 100:
        return False
    try:
        text, _ = decode_csv(data)
    except ValueError:
        return False
    sample = "\n".join(text.splitlines()[:12])
    return "," in sample and bool(re.search(r"(年月日|基準日|date|\\d{4}.?\\d{1,2}.?\\d{1,2})", sample, re.I))


def discover_candidates(page_url, expected_filename):
    html_bytes, final_url = fetch(page_url)
    text = html_bytes.decode("utf-8", errors="replace")
    parser = LinkParser()
    parser.feed(text)
    candidates = []

    for href, label in parser.links:
        absolute = urllib.parse.urljoin(final_url, href)
        if ".csv" in href.lower() or "csv" in label.lower() or "基準価額のデータ" in label:
            candidates.append(absolute)

    for match in re.findall(r'[^"\'<> ]+\\.csv(?:\\?[^"\'<> ]*)?', text, flags=re.I):
        candidates.append(urllib.parse.urljoin(final_url, match))

    base = urllib.parse.urljoin(final_url, "./")
    site = "https://www.alamco.co.jp/"
    candidates.extend([
        urllib.parse.urljoin(base, expected_filename),
        urllib.parse.urljoin(base, "csv/" + expected_filename),
        urllib.parse.urljoin(base, "data/" + expected_filename),
        urllib.parse.urljoin(site, "fund/" + expected_filename),
        urllib.parse.urljoin(site, "fund/csv/" + expected_filename),
        urllib.parse.urljoin(site, "fund/data/" + expected_filename),
        urllib.parse.urljoin(site, "common/csv/" + expected_filename),
        urllib.parse.urljoin(site, "common/data/" + expected_filename),
    ])

    result = []
    seen = set()
    for candidate in candidates:
        if candidate not in seen:
            seen.add(candidate)
            result.append(candidate)
    return result


def download_fund(page_url, expected_filename):
    errors = []
    for url in discover_candidates(page_url, expected_filename):
        try:
            data, final_url = fetch(url)
            if looks_like_price_csv(data):
                return data, final_url
            errors.append(url + ": invalid CSV")
        except Exception as exc:
            errors.append(url + ": " + str(exc))
    raise RuntimeError("Could not locate valid CSV:\n" + "\n".join(errors[-12:]))


def latest_info(data):
    text, encoding = decode_csv(data)
    rows = list(csv.reader(text.splitlines()))
    valid = [row for row in rows if len(row) >= 2 and re.search(r"\\d", row[0] or "")]
    return {
        "encoding": encoding,
        "rows": len(valid),
        "latest_date": valid[-1][0] if valid else None,
    }


def main():
    now_utc = dt.datetime.now(dt.timezone.utc)
    metadata = {
        "status": "ok",
        "updated_at": now_utc.isoformat(),
        "updated_at_jst": now_utc.astimezone(
            dt.timezone(dt.timedelta(hours=9))
        ).strftime("%Y/%m/%d %H:%M JST"),
        "funds": {},
    }

    for key, config in FUNDS.items():
        data, source_url = download_fund(config["page"], config["filename"])
        config["output"].write_bytes(data)
        metadata["funds"][key] = {
            "official_page": config["page"],
            "source_url": source_url,
            **latest_info(data),
        }
        print(key, len(data), source_url)

    (DATA_DIR / "update-info.json").write_text(
        json.dumps(metadata, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )


if __name__ == "__main__":
    main()
