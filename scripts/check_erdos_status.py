#!/usr/bin/env python3
"""Check if Erdos problem statuses in this repo match erdosproblems.com.

Downloads the latest problems.yaml from teorth/erdosproblems and compares
each problem's status against the @[category research open/solved] annotation
on the main theorem in the corresponding .lean file.

Usage:
  python check_erdos_status.py               # Print mismatches as JSON
  python check_erdos_status.py --problem 80  # Only that problem
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
CONJECTURES_URL = (
    "https://google-deepmind.github.io/formal-conjectures/data/conjectures.json"
)

# `open (Lean)` is the open counterpart of `solved (Lean)`: the problem is open and a Lean
# statement of it exists. Without it those problems are skipped rather than compared.
OPEN_STATES = {"open", "falsifiable", "verifiable", "open (Lean)"}
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


ERDOS_MODULE_RE = re.compile(r"^FormalConjectures\.ErdosProblems\.«?(\d+)»?$")


def fetch_conjectures():
    """The repository's own extract of every problem it states.

    `extract_names.lean` builds this from the Lean environment and the site publishes it, so
    it knows the category and formal-proof status of all 3551 problems exactly. Reading it
    beats re-deriving a subset here with regexes, which missed 23 Erdős problems whose main
    theorem is not spelled `erdos_<n>` and every problem whose attribute wraps a line.

    Set FC_CONJECTURES to a local path to use a freshly built one instead.
    """
    local = os.environ.get("FC_CONJECTURES")
    if local:
        with open(local) as f:
            return json.load(f)
    with urllib.request.urlopen(CONJECTURES_URL) as resp:
        return json.load(resp)


def problem_statuses(data=None):
    """Map problem number (str) -> 'open', 'solved', or 'formally solved'.

    A problem is open if any of its main statements is, formally solved if they are all
    solved and at least one carries an unconditional `formal_proof`, and solved otherwise.
    Variants and `test`/`API`/`textbook` statements do not count towards the status.
    """
    data = fetch_conjectures() if data is None else data
    rows = data.get("conjectures") or data.get("problems") or []
    by_problem, linked = {}, set()
    for row in rows:
        match = ERDOS_MODULE_RE.match(row.get("module", ""))
        if not match:
            continue
        num = match.group(1)
        # A `formal_proof` anywhere in the file counts, variants included, which is what the
        # attribute-scanning version this replaces did.
        #
        # Read `formalProofKind` rather than the link: a `formal_conjectures` proof lives in
        # this repository and is written with an empty link, so testing the link would drop
        # it. And skip a `conditional` proof, which is what `proofConditions` marks: it
        # establishes the statement only under hypotheses its author has not proved, so it
        # does not settle the problem.
        if row.get("formalProofKind") and not row.get("proofConditions"):
            linked.add(num)
        if is_variant(row.get("theorem", "")):
            continue
        if row.get("category") not in ("research open", "research solved"):
            continue
        by_problem.setdefault(num, []).append(row)

    result = {}
    for num, parts in by_problem.items():
        if any(p["category"] == "research open" for p in parts):
            result[num] = "open"
        elif num in linked:
            result[num] = "formally solved"
        else:
            result[num] = "solved"
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

    lean_statuses = problem_statuses()

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


def problem_argument(argv):
    """The value of `--problem N`, or None.

    A reviewer working on one problem should not have to read a repository-wide list and
    decide for themselves that their number is absent.
    """
    if "--problem" not in argv:
        return None
    index = argv.index("--problem")
    if index + 1 >= len(argv):
        sys.exit("--problem needs a problem number, for example --problem 80")
    return argv[index + 1]


def main():
    mismatches = find_mismatches()

    wanted = problem_argument(sys.argv)
    if wanted is not None:
        mismatches = [m for m in mismatches if m["number"] == wanted]
        json.dump(mismatches, sys.stdout, indent=2)
        print()
        # An empty list is the pass, and saying so beats printing `[]` at a reader.
        if not mismatches:
            print(f"Erdős problem {wanted}: the repository and erdosproblems.com agree.",
                  file=sys.stderr)
        return 1 if mismatches else 0

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
