#!/usr/bin/env python3
"""Check if Erdos problem statuses in this repo match erdosproblems.com.

Downloads the latest problems.yaml from teorth/erdosproblems and compares
each problem's status against the @[category research open/solved] annotation
on the main theorem in the corresponding .lean file.

Usage:
  python check_erdos_status.py               # Print mismatches as JSON
  python check_erdos_status.py --create-issues  # Also create GitHub issues
"""

import json
import os
import re
import subprocess
import sys
import urllib.request

YAML_URL = (
    "https://raw.githubusercontent.com/teorth/erdosproblems/main/data/problems.yaml"
)
ERDOS_DIR = os.path.join(
    os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
    "FormalConjectures",
    "ErdosProblems",
)

# Matches the category annotation line immediately before any erdos theorem.
# Captures the category and the problem number.
# Note: 'formally solved' is no longer a valid category value.
CATEGORY_THEN_THEOREM = re.compile(
    r"@\[category research (open|solved).*\]\s*\n"
    r"theorem erdos_(\d+)([\w.]*)\s",
    re.MULTILINE,
)

# Matches the formal_proof attribute (may appear on the same line as category or separate).
# Captures the proof kind.
FORMAL_PROOF_ATTR = re.compile(
    r"formal_proof using (formal_conjectures|lean4|other_system) at",
    re.MULTILINE,
)

OPEN_STATES = {"open", "falsifiable", "verifiable"}
SOLVED_STATES = {
    "solved",
    "proved",
    "disproved",
    "not provable",
    "not disprovable",
    "independent",
    "decidable",
}
FORMALLY_SOLVED_STATES = {
    "solved (Lean)",
    "proved (Lean)",
    "disproved (Lean)",
}


def fetch_yaml():
    # Imported here rather than at the top so the module can be imported without pyyaml,
    # which the tests do and the script-test CI job does not install.
    import yaml

    with urllib.request.urlopen(YAML_URL) as resp:
        return yaml.safe_load(resp.read())


def yaml_status_to_category(state):
    """Map a YAML status.state value to 'open', 'solved', 'formally solved', or None.

    Returns None for unrecognized states.
    """
    if state in OPEN_STATES:
        return "open"
    if state in FORMALLY_SOLVED_STATES:
        return "formally solved"
    if state in SOLVED_STATES:
        return "solved"
    print(f"WARNING: unrecognized YAML status state: {state!r}", file=sys.stderr)
    return None  # unrecognized — skip comparison


def lean_category(cat):
    """Normalize a captured category string to 'open' or 'solved'."""
    if cat == "open":
        return "open"
    return "solved"


def is_variant(suffix):
    """Check if a theorem name suffix indicates a variant (not a main part)."""
    return ".variants." in suffix


def scan_lean_files():
    """Return dict mapping problem number (str) -> 'open', 'solved', or 'formally solved'.

    For multi-part problems (no single `erdos_{N}` theorem), collects all
    non-variant theorems. The problem is 'open' if any part is open,
    'formally solved' if all parts are formally solved, and 'solved' otherwise.

    A problem is 'formally solved' if its category is 'solved' and it has a
    @[formal_proof ...] attribute.
    """
    result = {}
    for fname in os.listdir(ERDOS_DIR):
        if not fname.endswith(".lean"):
            continue
        file_number = fname.removesuffix(".lean")
        if not file_number.isdigit():
            continue
        filepath = os.path.join(ERDOS_DIR, fname)
        with open(filepath) as f:
            content = f.read()

        # Check if file has any formal_proof attribute
        has_formal_proof = bool(FORMAL_PROOF_ATTR.search(content))

        # Collect all non-variant theorem categories for this problem number
        main_categories = []
        has_exact_main = False
        exact_main_cat = None
        for m in CATEGORY_THEN_THEOREM.finditer(content):
            if m.group(2) != file_number:
                continue
            suffix = m.group(3)  # e.g. "", "_cycles", ".parts.i", ".variants.foo"
            cat = lean_category(m.group(1))
            # Upgrade to 'formally solved' if formal_proof attribute is present
            if cat == "solved" and has_formal_proof:
                cat = "formally solved"
            if suffix == "" or suffix == ":":
                # Exact match: `erdos_{N}` with no suffix
                has_exact_main = True
                exact_main_cat = cat
            elif not is_variant(suffix):
                main_categories.append(cat)

        if has_exact_main:
            # Single main theorem exists — use its category directly
            result[file_number] = exact_main_cat
        elif main_categories:
            # Multi-part problem: open if any part is open
            if "open" in main_categories:
                result[file_number] = "open"
            elif all(c == "formally solved" for c in main_categories):
                result[file_number] = "formally solved"
            else:
                result[file_number] = "solved"

    return result


def classifiable():
    """Problems the YAML gives a status this script understands.

    A problem missing from this set is not agreeing with us, it is one we cannot read, which
    is a different thing and must not be treated as resolved.
    """
    return {
        str(p["number"])
        for p in fetch_yaml()
        if yaml_status_to_category(p.get("status", {}).get("state", "open")) is not None
    }


def find_mismatches():
    problems = fetch_yaml()
    yaml_statuses = {}
    for p in problems:
        num = str(p["number"])
        state = p.get("status", {}).get("state", "open")
        cat = yaml_status_to_category(state)
        if cat is not None:
            yaml_statuses[num] = cat

    lean_statuses = scan_lean_files()

    mismatches = []
    for num, lean_cat in sorted(lean_statuses.items(), key=lambda x: int(x[0])):
        yaml_cat = yaml_statuses.get(num)
        if yaml_cat is None:
            continue  # problem not in YAML or has unrecognized status, skip
        if lean_cat != yaml_cat:
            mismatches.append(
                {
                    "number": num,
                    "lean_status": lean_cat,
                    "yaml_status": yaml_cat,
                }
            )
    return mismatches


def create_issues(mismatches):
    """Create GitHub issues for mismatches, skipping duplicates.

    Requires the `gh` CLI to be installed and GH_TOKEN to be set.
    """
    for m in mismatches:
        num = m["number"]
        title_prefix = f"Erdős Problem {num}: status mismatch"
        title = (
            f"{title_prefix} "
            f"(repo={m['lean_status']}, erdosproblems.com={m['yaml_status']})"
        )

        # Skip if an open issue with this prefix already exists
        result = subprocess.run(
            [
                "gh", "issue", "list",
                "--search", f"{title_prefix} in:title",
                "--state", "open",
                "--json", "number",
            ],
            capture_output=True,
            text=True,
        )
        if result.returncode != 0:
            print(
                f"Failed to check existing issues for Erdős Problem {num} "
                f"(gh exit code {result.returncode}), skipping to avoid "
                f"duplicates",
                file=sys.stderr,
            )
            continue
        existing = json.loads(result.stdout) if result.stdout.strip() else []
        if existing:
            print(f"Issue already exists for Erdős Problem {num}, skipping")
            continue

        body = (
            f"The status of [Erdős problem {num}]"
            f"(https://www.erdosproblems.com/{num}) "
            f"appears to have changed.\n\n"
            f"- **[This repo](http://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/{num}.lean)**: `{m['lean_status']}` "
            f"(in `FormalConjectures/ErdosProblems/{num}.lean`)\n"
            f"- **[erdosproblems.com/{num}](https://www.erdosproblems.com/{num})**: `{m['yaml_status']}`\n\n"
            f"Please verify and update the `@[category research ...]` "
            f"annotation if appropriate."
        )
        labels = ["erdos-status-sync"]
        if m["yaml_status"] == "formally solved":
            labels.append("formalisation exists elsewhere")
        cmd = ["gh", "issue", "create", "--title", title, "--body", body]
        for label in labels:
            cmd.extend(["--label", label])
        subprocess.run(cmd)


ISSUE_TITLE_RE = re.compile(r"Erdős Problem (\d+): status mismatch")


def issues_to_close(issues, still_open, known):
    """Which open sync issues no longer describe a real mismatch.

    Kept separate from the `gh` calls so it can be tested.
    """
    out = []
    for issue in issues:
        match = ISSUE_TITLE_RE.match(issue["title"])
        if not match:
            continue
        num = match.group(1)
        # Still mismatched, or a YAML state we cannot read. Either way, leave it alone:
        # "we cannot tell" is not the same as "resolved".
        if num in still_open or num not in known:
            continue
        out.append(issue["number"])
    return out


def close_resolved_issues(mismatches):
    """Close open sync issues whose mismatch has gone away.

    The script opens an issue when this repository and erdosproblems.com disagree, but
    nothing ever closed them, so the label accumulates issues describing a state that no
    longer holds. `mismatches` is everything still disagreeing, so any other open issue under
    the label has been overtaken by a merge.
    """
    # `find_mismatches` keys problems by string, so compare as strings.
    still_open = {str(m["number"]) for m in mismatches}
    known = classifiable()
    result = subprocess.run(
        [
            "gh", "issue", "list",
            "--label", "erdos-status-sync",
            "--state", "open",
            "--limit", "500",
            "--json", "number,title",
        ],
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        print(
            f"Failed to list sync issues (gh exit code {result.returncode}), "
            f"not closing anything",
            file=sys.stderr,
        )
        return
    issues = json.loads(result.stdout) if result.stdout.strip() else []
    for number in issues_to_close(issues, still_open, known):
        subprocess.run([
            "gh", "issue", "close", str(number),
            "--comment",
            "The repository and erdosproblems.com now agree on this problem, so there is "
            "no mismatch left to act on. Closed automatically; reopen if that is wrong.",
        ])


def main():
    mismatches = find_mismatches()
    json.dump(mismatches, sys.stdout, indent=2)
    print()  # trailing newline

    if "--create-issues" in sys.argv:
        if mismatches:
            create_issues(mismatches)
        # Runs even when nothing mismatches, which is exactly when there is most to close.
        close_resolved_issues(mismatches)

    return 1 if mismatches else 0


if __name__ == "__main__":
    sys.exit(main())
