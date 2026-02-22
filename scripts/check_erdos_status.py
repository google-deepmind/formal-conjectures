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

import yaml

YAML_URL = (
    "https://raw.githubusercontent.com/teorth/erdosproblems/main/data/problems.yaml"
)
ERDOS_DIR = os.path.join(
    os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
    "FormalConjectures",
    "ErdosProblems",
)

# Matches the category annotation line immediately before a main theorem.
# Captures the status word ("open" or "solved") and the problem number.
# The main theorem is `erdos_{N}` possibly followed by a suffix like `_statement`,
# but NOT containing a dot (which indicates a variant).
CATEGORY_THEN_THEOREM = re.compile(
    r"@\[category research (open|solved|formally solved[^]]*),.*\]\s*\n"
    r"theorem erdos_(\d+)\w*[\s:]",
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
    """Normalize a captured category string to 'open', 'solved', or 'formally solved'."""
    if cat == "open":
        return "open"
    if cat.startswith("formally solved"):
        return "formally solved"
    return "solved"


def scan_lean_files():
    """Return dict mapping problem number (str) -> 'open', 'solved', or 'formally solved'."""
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
        # Find the main theorem's category (first match for this problem number)
        for m in CATEGORY_THEN_THEOREM.finditer(content):
            if m.group(2) == file_number:
                result[file_number] = lean_category(m.group(1))
                break
    return result


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
        existing = json.loads(result.stdout) if result.stdout.strip() else []
        if existing:
            print(f"Issue already exists for Erdős Problem {num}, skipping")
            continue

        body = (
            f"The status of [Erdős problem {num}]"
            f"(https://www.erdosproblems.com/{num}) "
            f"appears to have changed.\n\n"
            f"- **This repo**: `{m['lean_status']}` "
            f"(in `FormalConjectures/ErdosProblems/{num}.lean`)\n"
            f"- **erdosproblems.com**: `{m['yaml_status']}`\n\n"
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


def main():
    mismatches = find_mismatches()
    json.dump(mismatches, sys.stdout, indent=2)
    print()  # trailing newline

    if "--create-issues" in sys.argv and mismatches:
        create_issues(mismatches)

    return 1 if mismatches else 0


if __name__ == "__main__":
    sys.exit(main())
