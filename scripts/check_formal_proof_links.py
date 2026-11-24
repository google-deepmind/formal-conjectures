#!/usr/bin/env python3
"""Check that every `formal_proof` link resolves and names the declaration it claims to prove.

A `formal_proof` attribute is the only evidence behind a `research solved` statement whose
proof lives outside this repository. Nothing else follows the link. This script does.

The links are read from the metadata that `scripts/extract_names.lean` writes, not from the
Lean sources: either the raw output (`{"problems": [...]}`, as written to
`site/data/conjectures.json` by the build) or the copy the website publishes
(`{"conjectures": [...]}`). By default the published copy is fetched, so no build is needed.
Each entry gives the full declaration name and its `formalProofs` (kind, link, conditions).

For each link:

1. Fetch the target. A GitHub `blob` URL is fetched as raw content. Report HTTP errors, and
   whether the Wayback Machine holds a copy, which helps re-pointing but is not the proof.
2. If the link has a line anchor (`#L123`), check that a `theorem`, `lemma` or `alias`
   declaration starts within a few lines of it. The keyword may follow modifiers, attributes
   or a custom command (`fc_compact_decl theorem ...`). An anchor that lands on nothing is
   stale. Report it.
3. If the link has no anchor and is a `formal_conjectures` link (a fork of this repository),
   check that a declaration whose name agrees with the annotated one exists in the target.
   Names agree when one equals the other or ends with it at a `.` boundary, so a namespace
   prefix on either side is allowed, but `erdos_1.parts.i` never stands in for
   `erdos_1.variants.i`. A fork keeps our names. Other kinds use their own names and are not
   checked.

The targets are external files that are not built here, so steps 2 and 3 read their text.
Comments and docstrings in a target are ignored: a `theorem` mentioned in a comment is not a
declaration. The check never under-reports a missing file or a missing name.

Usage:
  python check_formal_proof_links.py                       # findings as JSON; exit 1 on a defect
  python check_formal_proof_links.py site/data/conjectures.json   # read a local extract_names output
  python check_formal_proof_links.py --quiet               # only the summary line
  python check_formal_proof_links.py --offline             # list the links, fetch no targets

Exit status is 1 for `unreachable`, `anchor-not-on-declaration` and `name-not-found`.
"""

import argparse
import concurrent.futures
import json
import re
import sys
import urllib.error
import urllib.parse
import urllib.request

PUBLISHED_METADATA = "https://google-deepmind.github.io/formal-conjectures/data/conjectures.json"

USER_AGENT = "formal-conjectures/check_formal_proof_links"
TIMEOUT_SECONDS = 30
WORKERS = 8

# A `theorem`, `lemma` or `alias` and its name as written. `foo.{u}` is captured as `foo.`.
DECLARATION_NAME = re.compile(r"\b(?:theorem|lemma|alias)\s+([^\s:({]+)")

# A GitHub `blob` URL with optional line anchor `#L12` or range `#L12-L34`.
GITHUB_BLOB = re.compile(r"https://github\.com/([^/]+)/([^/]+)/blob/([^/]+)/(.+?)(?:#L(\d+)(?:-L(\d+))?)?$")

# Finding kinds that fail the run.
FAILING_KINDS = {"unreachable", "anchor-not-on-declaration", "name-not-found"}

# How far from a line anchor a declaration keyword may start. Anchors sometimes point at the
# attribute line above the `theorem`, and sometimes at the `:=` line below a long statement.
ANCHOR_SLACK_ABOVE = 12
ANCHOR_SLACK_BELOW = 3

# A line, comments blanked, that declares a theorem, lemma or alias. The keyword may follow
# attributes, modifiers or a custom command such as `fc_compact_decl`, so it is searched for
# anywhere on the line, as a whole word followed by a name.
DECLARATION_LINE = re.compile(r"(?<![\w.'])(?:theorem|lemma|alias)\s+[^\s:({]")


def mask_comments(text):
    """`text` with every comment and docstring replaced by spaces, keeping newlines, so offsets
    and line numbers are unchanged. Handles nested `/- -/` blocks and leaves string literals,
    where `--` is not a comment, alone."""
    out = list(text)
    i, n, depth = 0, len(text), 0
    while i < n:
        if depth == 0:
            if text[i] == '"':
                i += 1
                while i < n and text[i] != '"':
                    i += 2 if text[i] == "\\" else 1
                i += 1
            elif text.startswith("--", i):
                end = text.find("\n", i)
                end = n if end < 0 else end
                out[i:end] = " " * (end - i)
                i = end
            elif text.startswith("/-", i):
                depth = 1
                out[i:i + 2] = "  "
                i += 2
            else:
                i += 1
        elif text.startswith("/-", i):
            depth += 1
            out[i:i + 2] = "  "
            i += 2
        elif text.startswith("-/", i):
            depth -= 1
            out[i:i + 2] = "  "
            i += 2
        else:
            if text[i] != "\n":
                out[i] = " "
            i += 1
    return "".join(out)


def module_path(module):
    """`FormalConjectures.GreensOpenProblems.«52»` -> `FormalConjectures/GreensOpenProblems/52.lean`."""
    return module.replace("«", "").replace("»", "").replace(".", "/") + ".lean"


def links_from_metadata(metadata):
    """Return one record per formal proof in `extract_names` metadata, raw or published."""
    entries = metadata.get("problems")
    if entries is None:
        entries = metadata.get("conjectures")
    if entries is None:
        raise ValueError("metadata has neither `problems` nor `conjectures`")
    links = []
    for entry in entries:
        for proof in entry.get("formalProofs") or []:
            links.append(
                {
                    "file": entry.get("githubPath") or module_path(entry["module"]),
                    "name": entry["theorem"],
                    "kind": proof["kind"],
                    "url": proof["link"],
                    "conditions": proof.get("conditions") or [],
                }
            )
    links.sort(key=lambda l: (l["file"], l["name"], l["kind"], l["url"]))
    return links


def load_metadata(source):
    """Read `extract_names` metadata from a local path or an http(s) URL."""
    if source.startswith(("http://", "https://")):
        status, body = fetch(source)
        if status != 200:
            raise RuntimeError(f"could not fetch {source}: HTTP {status}")
        return json.loads(body)
    with open(source, encoding="utf-8") as f:
        return json.load(f)


def declares(content, name):
    """Whether `content` declares a theorem, lemma or alias whose name agrees with `name`
    (see `names_agree`). A declaration inside a namespace is found by its short name, but
    `erdos_1` is not found in `erdos_1.variants.two`, nor `erdos_1.variants.i` in
    `erdos_1.parts.i`. Universe parameters (`erdos_1.{u}`) are allowed. Comments are ignored."""
    return any(
        names_agree(m.group(1).rstrip("."), name)
        for m in DECLARATION_NAME.finditer(mask_comments(content))
    )


def names_agree(written, name):
    """Whether a declaration written as `written` can be the declaration `name`: equal, or one
    ends with the other at a `.` boundary. A namespace prefix on either side is allowed."""
    return written == name or written.endswith("." + name) or name.endswith("." + written)


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
    lines = mask_comments(body).splitlines()
    lo = max(0, first - 1 - ANCHOR_SLACK_ABOVE)
    hi = min(len(lines), last + ANCHOR_SLACK_BELOW)
    return any(DECLARATION_LINE.search(l) for l in lines[lo:hi])


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


def check_link(link, body_cache, wayback=True):
    """Return a list of findings for one link. Empty means the link is fine."""
    target = raw_url(link["url"])
    if target not in body_cache:
        body_cache[target] = fetch(target)
    status, body = body_cache[target]

    if status != 200:
        extra = {}
        if wayback:
            snapshot = wayback_snapshot(link["url"])
            extra["wayback"] = snapshot or "none"
        return [finding(link, "unreachable", f"HTTP {status}", **extra)]

    if not target.endswith(".lean"):
        return []  # not a Lean file; reachability is all that can be checked

    anchor = line_anchor(link["url"])
    if anchor is not None:
        if not declaration_near(body, anchor):
            return [finding(link, "anchor-not-on-declaration", f"no theorem or lemma near line {anchor[0]} of target")]
        return []

    if link["kind"] == "formal_conjectures" and not declares(body, link["name"]):
        return [finding(link, "name-not-found", f"no declaration named `{link['name']}` in target")]
    return []


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


def run(links, wayback=True):
    body_cache = {}
    # Fetch every distinct target once, in parallel, then check sequentially.
    targets = sorted({raw_url(l["url"]) for l in links})
    with concurrent.futures.ThreadPoolExecutor(WORKERS) as ex:
        for target, result in zip(targets, ex.map(fetch, targets)):
            body_cache[target] = result
    findings = []
    for link in links:
        findings.extend(check_link(link, body_cache, wayback=wayback))
    return findings


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("metadata", nargs="?", default=PUBLISHED_METADATA,
                        help="extract_names output, a path or URL (default: the published copy)")
    parser.add_argument("--quiet", action="store_true", help="print only the summary line")
    parser.add_argument("--offline", action="store_true", help="list the links without fetching targets")
    parser.add_argument("--no-wayback", action="store_true", help="do not query the Wayback Machine for dead links")
    args = parser.parse_args(argv)

    links = links_from_metadata(load_metadata(args.metadata))
    if args.offline:
        print(json.dumps(links, indent=2, ensure_ascii=False))
        return 0

    findings = run(links, wayback=not args.no_wayback)
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
