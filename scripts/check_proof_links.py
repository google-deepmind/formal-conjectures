#!/usr/bin/env python3
"""Check that every `formal_proof` link in the repo still resolves.

These links rot quietly. Nothing builds them and nothing reads them, so an
upstream rename or a typo in the path sits there until somebody clicks it. Two
were already dead when this script was written, both of them unpinned links to
a `main` branch that had since moved the file.

The links are read straight out of the `.lean` sources rather than from
`lake exe extract_names`, so this needs no Lean toolchain and no Mathlib build.

Usage:
  python check_proof_links.py                 # check every link
  python check_proof_links.py FILE [FILE ...] # check only these files
"""

import concurrent.futures
import pathlib
import re
import sys
import urllib.error
import urllib.request

ROOT = pathlib.Path(__file__).resolve().parent.parent

# `formal_proof using <kind> at "<link>"`, with the attribute free to wrap
# across lines the way it does in the problem files.
LINK = re.compile(
    r'formal_proof\s+using\s+\w+\s+at\s*\n?\s*"([^"]*)"',
    re.MULTILINE,
)

TIMEOUT = 30
ATTEMPTS = 3
# GitHub serves 403 to unadorned scripted requests often enough to matter.
HEADERS = {"User-Agent": "formal-conjectures-link-check"}


def display(path):
    """Path relative to the repo root, whichever form it arrived in."""
    try:
        return path.resolve().relative_to(ROOT)
    except ValueError:
        return path


def links_in(path):
    """Yield (path, line number, link) for each `formal_proof` link in `path`."""
    text = path.read_text(encoding="utf-8", errors="replace")
    for match in LINK.finditer(text):
        line = text.count("\n", 0, match.start()) + 1
        yield path, line, match.group(1)


def collect(paths):
    out = []
    for path in paths:
        if path.suffix == ".lean" and path.is_file():
            out.extend(links_in(path))
    return out


def check(link):
    """Return None if the link resolves, else a short reason.

    An empty link is not this script's business. It is allowed for the
    `formal_conjectures` kind, where the proof is this statement and there is
    nothing to point at, and the attribute itself already warns about an empty
    or malformed link for the kinds where one is required.
    """
    if not link or not link.startswith(("http://", "https://")):
        return None
    # A `#L79` fragment is for the reader; the server never sees it.
    url = link.split("#", 1)[0]
    last = "unknown error"
    for _ in range(ATTEMPTS):
        try:
            request = urllib.request.Request(url, headers=HEADERS)
            with urllib.request.urlopen(request, timeout=TIMEOUT) as response:
                if response.status == 200:
                    return None
                last = f"HTTP {response.status}"
        except urllib.error.HTTPError as error:
            # A 4xx is the link's fault and will not improve on a retry.
            if 400 <= error.code < 500:
                return f"HTTP {error.code}"
            last = f"HTTP {error.code}"
        except Exception as error:  # network flake, DNS, timeout
            last = type(error).__name__
    return last


def main(argv):
    if argv:
        paths = [pathlib.Path(a) for a in argv]
    else:
        paths = sorted(ROOT.glob("FormalConjectures/**/*.lean"))

    found = collect(paths)
    if not found:
        print("no formal_proof links found")
        return 0

    broken = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        results = pool.map(lambda entry: check(entry[2]), found)
        for (path, line, link), reason in zip(found, results):
            if reason is not None:
                broken.append((path, line, link, reason))

    print(f"checked {len(found)} formal_proof links, {len(broken)} broken")
    for path, line, link, reason in broken:
        print(f"\n{display(path)}:{line}: {reason}\n  {link}")

    if broken:
        print(
            "\nA link that has rotted usually means the file moved upstream. "
            "Prefer pinning to a commit rather than a branch."
        )
    return 1 if broken else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
