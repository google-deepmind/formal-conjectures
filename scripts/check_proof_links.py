#!/usr/bin/env python3
"""Print every `formal_proof` link in the repository, one per line.

These links rot quietly. Nothing builds them and nothing reads them, so an
upstream rename or a typo in the path sits there until somebody clicks it.

This script only answers the repository-specific question: which URLs are
`formal_proof` URLs? Checking that they resolve is a solved problem, and
`lychee` solves it, with the retries, backoff, status handling and
concurrency a bespoke checker would have to grow; the workflow in
`.github/workflows/check_proof_links.yml` pipes this script's output to it.
To find which file carries a link lychee reports broken, grep for the URL.

The links are read straight out of the `.lean` sources rather than from
`lake exe extract_names`, so this needs no Lean toolchain. When the
extract's `formalProofs` schema is the canonical metadata, this becomes a
`jq` line over it.

Usage:
  python check_proof_links.py                 # every link, once each
  python check_proof_links.py FILE [FILE ...] # only these files
"""

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent

# `formal_proof using <kind> at "<link>"`, with the attribute free to wrap
# across lines the way it does in the problem files.
LINK = re.compile(
    r'formal_proof\s+using\s+\w+\s+at\s*\n?\s*"([^"]*)"',
    re.MULTILINE,
)


def links_in(path):
    text = path.read_text(encoding="utf-8", errors="replace")
    return LINK.findall(text)


def main(argv):
    paths = ([pathlib.Path(a) for a in argv] if argv
             else sorted((ROOT / "FormalConjectures").rglob("*.lean")))
    seen = []
    for path in paths:
        if path.suffix == ".lean" and path.is_file():
            for link in links_in(path):
                if link and link not in seen:
                    seen.append(link)
    for link in seen:
        print(link)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
