#!/usr/bin/env python3
# Copyright 2025 The Formal Conjectures Authors.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""Print the LaTeX statement of an Erdős problem.

    python3 scripts/erdos_problem.py 940

Reads `erdosproblems.com/latex/<n>`, which serves the LaTeX the site renders,
and prints the statement, the remarks, the cross-referenced problems and the
reference list.

Prefer this to the rendered page. Rendering runs terms together, so that
`3^7\\cdot 61^5` reads as `3761^5`, and that misreading has already reached this
repository. The remarks matter as much as the statement: a status the site
records only in its remarks is a common source of a wrong `category`.

The site answers a request that identifies itself and refuses the default
`Python-urllib` user agent with a 403. This script sends an honest one naming
the tool. If another fetcher gets a 403, that is the cause, and the fix is to
name yourself rather than to imitate a browser.

`data/problems.yaml` in `teorth/erdosproblems`, which `check_erdos_status.py`
reads, carries status and tags only. It has no statement text, so it cannot
answer whether a formalisation matches its source.
"""

import argparse
import html
import re
import sys
import urllib.error
import urllib.request

URL = "https://www.erdosproblems.com/latex/{}"

USER_AGENT = (
    "formal-conjectures/erdos_problem.py "
    "(+https://github.com/google-deepmind/formal-conjectures)"
)

BLOCK = re.compile(
    r'<div[^>]*class="problem-(?:text|additional-text)"[^>]*>(.*?)</div>\s*</div>|'
    r'<div[^>]*class="problem-additional-text"[^>]*>(.*?)</div>',
    re.S,
)


def fetch(number):
    """The raw HTML of the LaTeX view, or exit with a readable message."""
    request = urllib.request.Request(
        URL.format(number), headers={"User-Agent": USER_AGENT}
    )
    try:
        with urllib.request.urlopen(request, timeout=30) as response:
            return response.read().decode("utf-8", errors="replace")
    except urllib.error.HTTPError as error:
        if error.code in (404, 500):
            sys.exit(
                f"erdosproblems.com returned HTTP {error.code} for problem {number}. "
                "Check that the problem exists."
            )
        sys.exit(f"erdosproblems.com returned HTTP {error.code} for problem {number}")
    except urllib.error.URLError as error:
        sys.exit(f"could not reach erdosproblems.com: {error.reason}")


def to_text(fragment):
    """One HTML fragment as plain LaTeX."""
    fragment = re.sub(r"<h3>(.*?)</h3>", r"\n## \1\n", fragment, flags=re.S)
    fragment = re.sub(r"<br\s*/?>", "\n", fragment)
    # A link to another problem renders as its number; keep it as [n].
    fragment = re.sub(r'<a[^>]*href="/(\d+)"[^>]*>.*?</a>', r"[\1]", fragment, flags=re.S)
    fragment = re.sub(r"<[^>]+>", "", fragment)
    fragment = html.unescape(fragment)
    fragment = "\n".join(line.strip() for line in fragment.split("\n"))
    fragment = re.sub(r"[ \t]+", " ", fragment)
    fragment = re.sub(r"\n{3,}", "\n\n", fragment)
    # The trailing "Back to the problem" link becomes a bare [n].
    fragment = re.sub(r"\n\s*\[\d+\]\s*$", "", fragment)
    return fragment.strip()


def blocks(page):
    """The statement and remark blocks, in the order the page gives them."""
    found = []
    for match in BLOCK.finditer(page):
        text = to_text(match.group(1) or match.group(2) or "")
        # The trailing "Back to the problem" link becomes a bare [n].
        if text and not re.fullmatch(r"\[\d+\]", text):
            found.append(text)
    return found


def cross_references(page):
    """Problem numbers this page links to, in order and without repeats."""
    seen = []
    for number in re.findall(r'<a[^>]*href="/(\d+)"', page):
        if number not in seen:
            seen.append(number)
    return seen


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("number", help="the problem number, for example 940")
    args = parser.parse_args(argv)

    page = fetch(args.number)
    found = blocks(page)
    if not found:
        sys.exit(
            f"could not find the statement of problem {args.number}. "
            "The page layout may have changed; read the page directly."
        )

    print(f"# Erdos problem {args.number}")
    print(f"# {URL.format(args.number)}")
    for text in found:
        print()
        print(text)

    linked = [n for n in cross_references(page) if n != str(args.number)]
    if linked:
        print()
        print("## See also")
        print(", ".join(f"[{n}]" for n in linked))
        print()
        print("# A wrong bound is often a correct bound copied from a neighbour")
        print("# whose statement differs. Read the problems above.")


if __name__ == "__main__":
    main()
