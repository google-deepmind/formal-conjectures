#!/usr/bin/env python3
"""Check that every `formal_proof` link resolves and names the declaration it claims to prove.

A `formal_proof` attribute is the only evidence behind a `research solved` statement whose
proof lives outside this repository. Nothing else follows the link. This script does.

For each `formal_proof using <kind> at "<url>"` in `FormalConjectures/`:

1. Fetch the target. A GitHub `blob` URL is fetched as raw content. Report HTTP errors, and
   whether the Wayback Machine holds a copy, which helps re-pointing but is not the proof.
2. If the link has a line anchor (`#L123`), check that a `theorem` or `lemma` starts within
   a few lines of it. An anchor that lands on nothing is stale. Report it.
3. If the link has no anchor and is a `formal_conjectures` link (a fork of this repository),
   check that a declaration with the same final name segment as the annotated one exists in
   the target. A fork keeps our names. Other kinds use their own names and are not checked.
4. With `--compare`, when the annotated declaration is also found by name in the target,
   compare the two statements (the text between the name and `:=`, whitespace and comments
   removed) and report a difference. A difference is not always a defect: an external proof
   may state the result in its own terms. It is always worth a look, which is why it is opt-in
   and never fails the run.

Statement comparison is textual. It cannot see through `abbrev`s, renamed binders, or
`open` namespaces, so it over-reports. It never under-reports a missing file or a missing name.

Usage:
  python check_formal_proof_links.py              # findings as JSON; exit 1 on a defect
  python check_formal_proof_links.py --compare    # also report statement differences
  python check_formal_proof_links.py --quiet      # only the summary line
  python check_formal_proof_links.py --offline    # parse and list the links, no network

Exit status is 1 only for `unreachable`, `anchor-not-on-declaration` and `name-not-found`.
"""

import argparse
import concurrent.futures
import json
import os
import re
import sys
import urllib.error
import urllib.parse
import urllib.request

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CONJECTURES_DIR = os.path.join(REPO_ROOT, "FormalConjectures")

USER_AGENT = "formal-conjectures/check_formal_proof_links"
TIMEOUT_SECONDS = 30
WORKERS = 8

# An attribute block `@[...]`, allowing one level of nested brackets.
ATTRIBUTE_BLOCK = re.compile(r"@\[(?:[^\[\]]|\[[^\]]*\])*?\]", re.DOTALL)

# One `formal_proof` tag inside an attribute block.
FORMAL_PROOF_TAG = re.compile(r'formal_proof\s+using\s+(\w+)\s+at\s+"([^"]+)"')

# The declaration that follows an attribute block.
DECLARATION_AFTER = re.compile(r"\s*(?:private\s+|protected\s+)?(?:theorem|lemma|def)\s+([^\s:({]+)")

# A GitHub `blob` URL with optional line anchor `#L12` or range `#L12-L34`.
GITHUB_BLOB = re.compile(r"https://github\.com/([^/]+)/([^/]+)/blob/([^/]+)/(.+?)(?:#L(\d+)(?:-L(\d+))?)?$")

LINE_COMMENT = re.compile(r"--[^\n]*")

# Finding kinds that fail the run. `statement-differs` is advisory.
FAILING_KINDS = {"unreachable", "anchor-not-on-declaration", "name-not-found"}

# How far from a line anchor a declaration keyword may start. Anchors sometimes point at the
# attribute line above the `theorem`, and sometimes at the `:=` line below a long statement.
ANCHOR_SLACK_ABOVE = 12
ANCHOR_SLACK_BELOW = 3

DECLARATION_LINE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(?:theorem|lemma)\b")


def find_links(root=CONJECTURES_DIR):
    """Return one record per `formal_proof` tag under `root`."""
    links = []
    for dirpath, _, filenames in sorted(os.walk(root)):
        for fname in sorted(filenames):
            if not fname.endswith(".lean"):
                continue
            path = os.path.join(dirpath, fname)
            with open(path, encoding="utf-8") as f:
                content = f.read()
            rel = os.path.relpath(path, REPO_ROOT).replace(os.sep, "/")
            for block in ATTRIBUTE_BLOCK.finditer(content):
                tags = FORMAL_PROOF_TAG.findall(block.group(0))
                if not tags:
                    continue
                decl = DECLARATION_AFTER.match(content, block.end())
                name = decl.group(1) if decl else None
                statement = declaration_statement(content, name) if name else None
                for kind, url in tags:
                    links.append(
                        {
                            "file": rel,
                            "name": name,
                            "kind": kind,
                            "url": url,
                            "statement": statement,
                        }
                    )
    return links


def declaration_statement(content, name):
    """The statement text of `name` in `content`: from after the name to the first `:=`.

    Returns None when the declaration is not found. Matches on the final name segment so a
    declaration written inside a namespace is found by its short name.
    """
    short = name.rsplit(".", 1)[-1]
    pattern = re.compile(
        r"\b(?:theorem|lemma)\s+(?:[\w.'«»]*\.)?" + re.escape(short) + r"(?![\w'])"
    )
    m = pattern.search(content)
    if not m:
        return None
    rest = content[m.end():]
    end = rest.find(":=")
    return rest if end < 0 else rest[:end]


def normalise(statement):
    """Strip line comments and all whitespace so two statements can be compared."""
    if statement is None:
        return None
    return re.sub(r"\s+", "", LINE_COMMENT.sub("", statement))


def raw_url(url):
    """Map a GitHub `blob` URL to the raw file; leave other URLs unchanged."""
    m = GITHUB_BLOB.match(url)
    if not m:
        return url
    owner, repo, ref, path, _, _ = m.groups()
    return f"https://raw.githubusercontent.com/{owner}/{repo}/{ref}/{path}"


def line_anchor(url):
    """The `(first, last)` lines of a `#L12` or `#L12-L34` anchor, or None."""
    m = GITHUB_BLOB.match(url)
    if not m or not m.group(5):
        return None
    first = int(m.group(5))
    last = int(m.group(6)) if m.group(6) else first
    return first, last


def declaration_near(body, anchor):
    """Whether a `theorem`/`lemma` starts near the anchor `(first, last)` (1-based): up to
    `ANCHOR_SLACK_ABOVE` lines before `first` or `ANCHOR_SLACK_BELOW` after `last`."""
    first, last = anchor
    lines = body.splitlines()
    lo = max(0, first - 1 - ANCHOR_SLACK_ABOVE)
    hi = min(len(lines), last + ANCHOR_SLACK_BELOW)
    return any(DECLARATION_LINE.match(l) for l in lines[lo:hi])


def fetch(url):
    """Return (status, body). `status` is an int HTTP code or an error string."""
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    try:
        with urllib.request.urlopen(req, timeout=TIMEOUT_SECONDS) as resp:
            return resp.status, resp.read().decode("utf-8", "replace")
    except urllib.error.HTTPError as e:
        return e.code, ""
    except Exception as e:  # network errors, timeouts
        return type(e).__name__, ""


WAYBACK_CDX = "https://web.archive.org/cdx/search/cdx?output=json&limit=1&fl=timestamp&filter=statuscode:200&url="


def wayback_snapshot(url):
    """The date (YYYYMMDD) of the most recent Wayback Machine capture of `url`, or None.

    A snapshot is help for re-pointing a dead link, not a substitute for it: a fork that was
    rebased usually means the proof changed. The result is reported, never used to clear a
    finding. Rate limited by archive.org, so this is called only for unreachable targets.
    """
    page = url.split("#")[0]
    status, body = fetch(WAYBACK_CDX + urllib.parse.quote(page, safe=""))
    if status != 200:
        return None
    try:
        rows = json.loads(body)
    except ValueError:
        return None
    return rows[1][0][:8] if len(rows) > 1 and rows[1] else None


def check_link(link, body_cache, compare=True, wayback=True):
    """Return a list of findings for one link. Empty means the link is fine."""
    target = raw_url(link["url"])
    if target not in body_cache:
        body_cache[target] = fetch(target)
    status, body = body_cache[target]

    findings = []
    if status != 200:
        extra = {}
        if wayback:
            snapshot = wayback_snapshot(link["url"])
            extra["wayback"] = snapshot or "none"
        findings.append(finding(link, "unreachable", f"HTTP {status}", **extra))
        return findings

    if not target.endswith(".lean") or link["name"] is None:
        return findings  # not a Lean file, or no declaration to compare; nothing more to check

    anchor = line_anchor(link["url"])
    if anchor is not None and not declaration_near(body, anchor):
        findings.append(
            finding(link, "anchor-not-on-declaration", f"no theorem or lemma near line {anchor[0]} of target")
        )
        return findings

    linked_statement = declaration_statement(body, link["name"])
    if linked_statement is None:
        if anchor is None and link["kind"] == "formal_conjectures":
            findings.append(
                finding(link, "name-not-found", f"no declaration named `{link['name']}` in target")
            )
        return findings

    if compare and link["statement"] is not None:
        if normalise(link["statement"]) != normalise(linked_statement):
            findings.append(
                finding(
                    link,
                    "statement-differs",
                    "statement at target differs from statement here",
                    here=" ".join(link["statement"].split()),
                    there=" ".join(linked_statement.split()),
                )
            )
    return findings


def finding(link, kind, detail, **extra):
    record = {
        "kind": kind,
        "file": link["file"],
        "name": link["name"],
        "url": link["url"],
        "detail": detail,
    }
    record.update(extra)
    return record


def run(links, compare=True, wayback=True):
    body_cache = {}
    # Fetch every distinct target once, in parallel, then check sequentially.
    targets = sorted({raw_url(l["url"]) for l in links})
    with concurrent.futures.ThreadPoolExecutor(WORKERS) as ex:
        for target, result in zip(targets, ex.map(fetch, targets)):
            body_cache[target] = result
    findings = []
    for link in links:
        findings.extend(check_link(link, body_cache, compare=compare, wayback=wayback))
    return findings


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--quiet", action="store_true", help="print only the summary line")
    parser.add_argument("--compare", action="store_true", help="also report statement differences")
    parser.add_argument("--offline", action="store_true", help="list links without fetching")
    parser.add_argument("--no-wayback", action="store_true", help="do not query the Wayback Machine for dead links")
    args = parser.parse_args(argv)

    links = find_links()
    if args.offline:
        print(json.dumps(links, indent=2, ensure_ascii=False))
        return 0

    findings = run(links, compare=args.compare, wayback=not args.no_wayback)
    if not args.quiet:
        print(json.dumps(findings, indent=2, ensure_ascii=False))
    counts = {}
    for f in findings:
        counts[f["kind"]] = counts.get(f["kind"], 0) + 1
    summary = ", ".join(f"{k}: {v}" for k, v in sorted(counts.items())) or "none"
    print(f"{len(links)} formal_proof links checked; findings: {summary}", file=sys.stderr)
    return 1 if any(f["kind"] in FAILING_KINDS for f in findings) else 0


if __name__ == "__main__":
    sys.exit(main())
