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

By default the links are read straight out of the `.lean` sources, so the
existing workflow needs no Lean toolchain. `--extract` accepts a canonical
schema-2 extract and strictly enumerates every nonempty
`formalProofs[].link`; it is available for consumer convergence but does not
become the workflow default until #4894 lands.

Usage:
  python check_proof_links.py                 # every link, once each
  python check_proof_links.py FILE [FILE ...] # only these files
  python check_proof_links.py --extract conjectures.json
"""

import json
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


def unique_links(links):
    """Return nonempty links once each, preserving deterministic input order."""
    seen = set()
    result = []
    for link in links:
        if link and link not in seen:
            seen.add(link)
            result.append(link)
    return result


def links_from_extract(path):
    """Read every link from a closed canonical schema-2 metadata extract."""
    data = json.loads(path.read_text(encoding="utf-8"))
    if data.get("schemaVersion") != 2:
        raise ValueError("--extract requires schemaVersion 2")
    if "conjectures" in data:
        rows = data["conjectures"]
    elif "problems" in data:
        rows = data["problems"]
    else:
        raise ValueError("schema 2 extract has no declaration rows")
    if not isinstance(rows, list):
        raise ValueError("schema 2 declaration rows must be a list")
    links = []
    for row_index, row in enumerate(rows):
        if not isinstance(row, dict):
            raise ValueError(f"schema 2 row {row_index} must be an object")
        proofs = row.get("formalProofs")
        if not isinstance(proofs, list):
            raise ValueError(
                f"schema 2 row {row_index} formalProofs must be a list")
        for proof_index, proof in enumerate(proofs):
            if not isinstance(proof, dict):
                raise ValueError(
                    f"schema 2 row {row_index} proof {proof_index} must be an object")
            link = proof.get("link")
            if not isinstance(link, str):
                raise ValueError(
                    f"schema 2 row {row_index} proof {proof_index} link must be a string")
            links.append(link)
    return unique_links(links)


def main(argv):
    if argv[:1] == ["--extract"]:
        if len(argv) != 2:
            raise SystemExit("usage: check_proof_links.py --extract FILE")
        for link in links_from_extract(pathlib.Path(argv[1])):
            print(link)
        return 0
    paths = ([pathlib.Path(a) for a in argv] if argv
             else sorted((ROOT / "FormalConjectures").rglob("*.lean")))
    links = []
    for path in paths:
        if path.suffix == ".lean" and path.is_file():
            for link in links_in(path):
                links.append(link)
    for link in unique_links(links):
        print(link)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
