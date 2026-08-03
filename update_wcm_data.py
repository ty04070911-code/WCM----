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
        "expected": "171514_price.csv",
        "output": DATA_DIR / "wcm_distribution.csv",
    },
    "growth": {
        "page": "https://www.alamco.co.jp/fund/WCM_ag/index.html",
        "expected": "170514_price.csv",
        "output": DATA_DIR / "wcm_growth.csv",
    },
}

HEADERS = {
    "User-Agent": "Mozilla/5.0 (compatible; WCMAnalyzerUpdater/22.1)",
    "Accept": "text/html,text/csv,text/plain,application/octet-stream;q=0.9,*/*;q=0.8",
}


class LinkParser(html.parser.HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.links: list[tuple[str, str]] = []
        self._href: str | None = None
        self._text: list[str] = []

    def handle_starttag(self, tag: str, attrs) -> None:
        if tag.lower() == "a":
            self._href = dict(attrs).get("href")
            self._text = []

    def handle_data(self, data: str) -> None:
        if self._href is not None:
            self._text.append(data)

    def handle_endtag(self, tag: str) -> None:
        if tag.lower() == "a" and self._href is not None:
            self.links.append((self._href, "".join(self._text).strip()))
            self._href = None
            self._text = []


def fetch(url: str) -> tuple[bytes, str]:
    request = urllib.request.Request(url, headers=HEADERS)
    with urllib.request.urlopen(request, timeout=45) as response:
        return response.read(), response.geturl()


def decode_csv(data: bytes) -> tuple[str, str]:
    for encoding in ("cp932", "shift_jis", "utf-8-sig", "utf-8"):
        try:
            return data.decode(encoding), encoding
        except UnicodeDecodeError:
            continue
    raise ValueError("Unsupported CSV encoding")


def looks_like_price_csv(data: bytes) -> bool:
    if len(data) < 100:
        return False
    try:
        text, _ = decode_csv(data)
    except ValueError:
        return False
    sample = "\n".join(text.splitlines()[:15])
    return (
        "," in sample
        and bool(re.search(r"(年月日|基準日|date|\d{4}.?\d{1,2}.?\d{1,2})", sample, re.I))
        and bool(re.search(r"\d{3,}", sample))
    )


def discover_candidates(page_url: str, expected: str) -> list[str]:
    page_data, final_page_url = fetch(page_url)
    page_text = page_data.decode("utf-8", errors="replace")

    parser = LinkParser()
    parser.feed(page_text)

    candidates: list[str] = []

    for href, label in parser.links:
        absolute = urllib.parse.urljoin(final_page_url, href)
        if (
            ".csv" in href.lower()
            or "csv" in label.lower()
            or "基準価額" in label
            or "データ" in label
        ):
            candidates.append(absolute)

    for match in re.findall(
        r"""[^"'<> ]+\.csv(?:\?[^"'<> ]*)?""",
        page_text,
        flags=re.I,
    ):
        candidates.append(urllib.parse.urljoin(final_page_url, match))

    base = urllib.parse.urljoin(final_page_url, "./")
    root = "https://www.alamco.co.jp/"
    candidates.extend(
        [
            urllib.parse.urljoin(base, expected),
            urllib.parse.urljoin(base, f"csv/{expected}"),
            urllib.parse.urljoin(base, f"data/{expected}"),
            urllib.parse.urljoin(root, f"fund/{expected}"),
            urllib.parse.urljoin(root, f"fund/csv/{expected}"),
            urllib.parse.urljoin(root, f"fund/data/{expected}"),
            urllib.parse.urljoin(root, f"common/csv/{expected}"),
            urllib.parse.urljoin(root, f"common/data/{expected}"),
        ]
    )

    result: list[str] = []
    seen: set[str] = set()
    for candidate in candidates:
        if candidate not in seen:
            seen.add(candidate)
            result.append(candidate)
    return result


def download_fund(page_url: str, expected: str) -> tuple[bytes, str]:
    errors: list[str] = []

    for candidate in discover_candidates(page_url, expected):
        try:
            data, final_url = fetch(candidate)
            if looks_like_price_csv(data):
                return data, final_url
            errors.append(f"{candidate}: not a valid price CSV")
        except Exception as exc:  # noqa: BLE001
            errors.append(f"{candidate}: {exc}")

    raise RuntimeError(
        "Could not locate a valid price CSV.\n"
        + "\n".join(errors[-15:])
    )


def latest_info(data: bytes) -> dict[str, object]:
    text, encoding = decode_csv(data)
    rows = list(csv.reader(text.splitlines()))
    valid = [
        row
        for row in rows
        if len(row) >= 2 and re.search(r"\d", row[0] or "")
    ]

    return {
        "encoding": encoding,
        "rows": len(valid),
        "latest_date": valid[-1][0] if valid else None,
    }


def main() -> None:
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
        data, source_url = download_fund(
            config["page"],
            config["expected"],
        )
        config["output"].write_bytes(data)
        metadata["funds"][key] = {
            "official_page": config["page"],
            "source_url": source_url,
            **latest_info(data),
        }
        print(f"{key}: {len(data):,} bytes from {source_url}")

    (DATA_DIR / "update-info.json").write_text(
        json.dumps(metadata, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )


if __name__ == "__main__":
    main()
