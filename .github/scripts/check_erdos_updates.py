#!/usr/bin/env python3
"""Scan Lean files under an Erdos problems directory, fetch the referenced
Erdos problem pages, extract a last-updated date (if present), compare with
previously saved dates, and emit a JSON list of updates.

Behavior:
- On first run (empty dates file), populate the dates file and exit with no
  updates to avoid creating a flood of issues.
- On subsequent runs, produce an updates JSON array for changed dates.
"""
import argparse
import os
import re
import json
import sys
from glob import glob

import requests
try:
    from bs4 import BeautifulSoup
except Exception:
    BeautifulSoup = None
from dateutil import parser as dateparser


def find_erdos_url(text):
    m = re.search(r"https?://(?:www\.)?erdosproblems\.com/(\d+)", text)
    if m:
        return f"https://www.erdosproblems.com/{m.group(1)}", m.group(1)
    return None, None


def extract_date_from_page(text):
    # Prefer explicit "last edited" phrasing used on erdosproblems.com
    m = re.search(r"last\s+(?:edited|updated)[^\d\n\r]*(\d{1,2} [A-Za-z]+ \d{4}|[A-Za-z]+ \d{1,2},? \d{4}|\d{4}-\d{2}-\d{2})",
                  text, re.I)
    if m:
        try:
            return dateparser.parse(m.group(1)).date().isoformat()
        except Exception:
            pass

    # Try ISO-like date anywhere
    m = re.search(r"(\d{4}-\d{2}-\d{2})", text)
    if m:
        try:
            return dateparser.parse(m.group(1)).date().isoformat()
        except Exception:
            pass

    # If BeautifulSoup is available, search for strings that mention 'update'
    nodes = []
    if BeautifulSoup is not None:
        try:
            soup = BeautifulSoup(text, "html.parser")
            for node in soup.find_all(string=re.compile(r"update|edited|last", re.I)):
                nodes.append(str(node))
        except Exception:
            nodes = []

    for cand in nodes:
        # try common formats in the candidate strings
        m = re.search(r"(\d{4}-\d{2}-\d{2})", cand)
        if m:
            try:
                return dateparser.parse(m.group(1)).date().isoformat()
            except Exception:
                pass
        m = re.search(r"(\d{1,2} [A-Za-z]+ \d{4})", cand)
        if m:
            try:
                return dateparser.parse(m.group(1)).date().isoformat()
            except Exception:
                pass
        m = re.search(r"([A-Za-z]+ \d{1,2},? \d{4})", cand)
        if m:
            try:
                return dateparser.parse(m.group(1)).date().isoformat()
            except Exception:
                pass

    # Final fallback: look for month-name day, year anywhere in text
    m = re.search(r"([A-Za-z]+ \d{1,2},? \d{4})", text)
    if m:
        try:
            return dateparser.parse(m.group(1)).date().isoformat()
        except Exception:
            pass

    return None


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--problems-dir", required=False,
                   help="Path to directory containing Erdos .lean files")
    p.add_argument("--dates-file", required=False,
                   help="Path to JSON file storing last-seen dates")
    p.add_argument("--out", required=False,
                   help="Path to write updates JSON file")
    p.add_argument("--dry-run", action="store_true",
                   help="Don't write files; print detected updates to stdout")
    p.add_argument("--sample-html", required=False,
                   help="Parse a single local HTML file to test date extraction")
    p.add_argument("--id", required=False,
                   help="Problem id to associate with --sample-html output")
    p.add_argument("--lean-path", required=False,
                   help="Lean file path to include in sample output")
    args = p.parse_args()

    problems_dir = args.problems_dir
    dates_file = args.dates_file
    out_file = args.out
    dry_run = args.dry_run
    sample_html = args.sample_html
    sample_id = args.id
    sample_lean = args.lean_path

    # If sample mode is used, parse a local HTML file and print result
    if sample_html:
        if not os.path.exists(sample_html):
            print(f"Sample HTML file not found: {sample_html}", file=sys.stderr)
            return 2
        with open(sample_html, "r", encoding="utf8") as f:
            html = f.read()
        date = extract_date_from_page(html)
        print(json.dumps({
            "id": sample_id,
            "lean_path": sample_lean,
            "url": None,
            "extracted_date": date
        }, indent=2))
        return 0

    # load existing dates (if provided)
    if dates_file and os.path.exists(dates_file):
        with open(dates_file, "r", encoding="utf8") as f:
            try:
                dates = json.load(f)
            except Exception:
                dates = {}
    else:
        dates = {}

    discovered = {}
    updates = []

    if not problems_dir:
        print("Error: --problems-dir is required unless using --sample-html", file=sys.stderr)
        return 2

    files = glob(os.path.join(problems_dir, "*.lean"))
    for fp in files:
        try:
            with open(fp, "r", encoding="utf8") as f:
                txt = f.read()
        except Exception:
            continue

        url, pid = find_erdos_url(txt)
        if not url:
            continue

        # fetch page
        try:
            headers = {"User-Agent": "formal-conjectures/erdos-watcher (+https://github.com)"}
            r = requests.get(url, headers=headers, timeout=20)
            if r.status_code != 200:
                print(f"Warning: cannot fetch {url}: {r.status_code}", file=sys.stderr)
                page_date = None
            else:
                page_date = extract_date_from_page(r.text)
        except Exception as e:
            print(f"Warning: request failed for {url}: {e}", file=sys.stderr)
            page_date = None

        discovered[pid] = page_date

        old = dates.get(pid)
        # If dates file is empty (initial run) we will only populate it and not
        # create updates. We handle that after scanning.
        if old is None and dates:
            # If there was previously no date recorded for this id, treat as update
            if page_date is not None:
                updates.append({"id": pid, "url": url, "old": None, "new": page_date, "lean_path": fp})
        elif old is not None:
            if page_date != old:
                updates.append({"id": pid, "url": url, "old": old, "new": page_date, "lean_path": fp})

    # If this is the first run (dates was empty), populate it and exit with no updates
    if not dates:
        if dry_run:
            print("Dry-run: would initialize dates with:")
            print(json.dumps(discovered, indent=2))
            with open(out_file or "-", "w", encoding="utf8") as f:
                if out_file:
                    json.dump([], f, indent=2, ensure_ascii=False)
            print("Initialized dates (dry-run). No updates emitted on first run.")
            return 0
        else:
            if dates_file:
                with open(dates_file, "w", encoding="utf8") as f:
                    json.dump(discovered, f, indent=2, ensure_ascii=False)
            if out_file:
                with open(out_file, "w", encoding="utf8") as f:
                    json.dump([], f, indent=2, ensure_ascii=False)
            print("Initialized dates file; no updates emitted on first run.")
            return 0

    # write updated dates and updates list
    # merge discovered into dates (keep existing values for pages we couldn't fetch)
    for k, v in discovered.items():
        dates[k] = v

    # write updated dates and updates list (unless dry-run)
    if dry_run:
        print("Dry-run mode enabled. Detected updates:")
        print(json.dumps(updates, indent=2))
        print("Dry-run: merged dates would be:")
        merged = dates.copy()
        for k, v in discovered.items():
            merged[k] = v
        print(json.dumps(merged, indent=2))
        return 0

    # normal mode: persist files
    if dates_file:
        os.makedirs(os.path.dirname(dates_file), exist_ok=True)
        with open(dates_file, "w", encoding="utf8") as f:
            json.dump(dates, f, indent=2, ensure_ascii=False)

    if out_file:
        os.makedirs(os.path.dirname(out_file), exist_ok=True)
        with open(out_file, "w", encoding="utf8") as f:
            json.dump(updates, f, indent=2, ensure_ascii=False)

    if updates:
        print(f"Detected {len(updates)} updates")
    else:
        print("No updates detected")

    return 0


if __name__ == "__main__":
    sys.exit(main())
