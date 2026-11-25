#!/usr/bin/env python3
"""Check if Erdos problem statuses in this repo match erdosproblems.com.

Downloads the latest problems.yaml from teorth/erdosproblems and compares
each problem's status against the @[category research open/solved] annotation
on the main theorem in the corresponding .lean file.

The upstream side is read from the `informal_status` and `formal_status` fields, not from the
`status` string that joins them.

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

# `informal_status.state` is the mathematical status, and these two sets are the whole of its
# vocabulary. `formal_status.state` separately says whether a machine-checked proof exists.
# Upstream also publishes the two joined into `status.state` ("proved (Lean)"), but that is a
# product of two vocabularies and gains a value whenever either side does, so the code reads
# the two fields instead of their combinations.
#
# The split below follows the definitions in the upstream CONTRIBUTING.md. Three of these
# states name a problem that is still open: "decidable" is "both falsifiable and verifiable,
# but not yet solved", and "not provable" and "not disprovable" are each "open in general",
# with a model of set theory that settles the problem one way. "independent" is a resolution,
# so it counts as solved.
OPEN_STATES = {
    "open",
    "falsifiable",
    "verifiable",
    "decidable",
    "not provable",
    "not disprovable",
}
SOLVED_STATES = {"solved", "proved", "disproved", "independent"}

# Upstream states this value explicitly and never leaves it blank, and every other value
# names a proof assistant. CONTRIBUTING.md reserves the right to add assistants, and 6
# problems already carry an undocumented "formalized", so the code tests this one value
# rather than a list that would skip a problem whenever upstream adds a name.
UNFORMALIZED_STATE = "unformalized"


def fetch_yaml():
    # Imported here rather than at the top so the module can be imported without pyyaml,
    # which the tests do and the script-test CI job does not install.
    import yaml

    with urllib.request.urlopen(YAML_URL) as resp:
        return yaml.safe_load(resp.read())


def problem_status(problem):
    """The (informal, formal) status states of a YAML problem.

    Each default claims the least. An absent, null or empty formal state records no
    formalisation, so a settled problem degrades to 'solved' and the code does not invent
    a proof. An absent informal state is not a status at all, so it falls into the
    warn-and-skip path below and does not assert that the problem is open.
    """
    informal = (problem.get("informal_status") or {}).get("state")
    formal = (problem.get("formal_status") or {}).get("state") or UNFORMALIZED_STATE
    return informal, formal


def yaml_status_to_category(informal_state, formal_state):
    """Map a problem's YAML status states to 'open', 'solved', 'formally solved', or None.

    A problem is 'formally solved' when it is settled and upstream records a formalisation.
    An open problem stays open even when a Lean statement of it exists, which is how
    `scan_lean_files` reads this repository: it upgrades a problem to 'formally solved' only
    when the category is already 'solved'.

    Returns None for an informal state this script does not know, which means "we cannot read
    this problem", not "this problem agrees with us".
    """
    if informal_state in OPEN_STATES:
        return "open"
    if informal_state in SOLVED_STATES:
        if formal_state != UNFORMALIZED_STATE:
            return "formally solved"
        return "solved"
    print(
        f"WARNING: unrecognized YAML informal status state: {informal_state!r}",
        file=sys.stderr,
    )
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
        if yaml_status_to_category(*problem_status(p)) is not None
    }


def find_mismatches():
    problems = fetch_yaml()
    yaml_statuses = {}
    for p in problems:
        num = str(p["number"])
        cat = yaml_status_to_category(*problem_status(p))
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


ISSUE_TITLE_RE = re.compile(r"Erdős Problem (\d+): status mismatch")


def issue_title(m):
    """The title of the sync issue for mismatch `m`, which records both computed sides."""
    return (
        f"Erdős Problem {m['number']}: status mismatch "
        f"(repo={m['lean_status']}, erdosproblems.com={m['yaml_status']})"
    )


SYNC_LABEL = "erdos-status-sync"
FORMALISED_LABEL = "formalisation exists elsewhere"


def issue_labels(m):
    labels = [SYNC_LABEL]
    if m["yaml_status"] == "formally solved":
        labels.append(FORMALISED_LABEL)
    return labels


def label_changes(m, issue):
    """The labels to add to and remove from `issue`, as `(to_add, to_remove)`.

    Only the labels that this script manages are removed.
    """
    current = {label["name"] for label in issue["labels"]}
    wanted = issue_labels(m)
    to_add = [label for label in wanted if label not in current]
    to_remove = [
        label
        for label in (SYNC_LABEL, FORMALISED_LABEL)
        if label in current and label not in wanted
    ]
    return to_add, to_remove


ISSUE_LIST_LIMIT = 1000


def list_sync_issues():
    """The open issues under the sync label, or None if `gh` fails.

    This lists the label directly instead of going through GitHub search. Search can lag
    behind or come back empty, and an empty result made the script open a second issue for a
    problem that already had one.
    """
    result = subprocess.run(
        [
            "gh", "issue", "list",
            "--label", SYNC_LABEL,
            "--state", "open",
            "--limit", str(ISSUE_LIST_LIMIT),
            "--json", "number,title,labels",
        ],
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        print(
            f"Failed to list sync issues (gh exit code {result.returncode})",
            file=sys.stderr,
        )
        return None
    issues = json.loads(result.stdout) if result.stdout.strip() else []
    if len(issues) >= ISSUE_LIST_LIMIT:
        # The list may be cut off. A missing issue would be opened again as a duplicate.
        print(f"Listed {len(issues)} sync issues, the limit; the list may be incomplete",
              file=sys.stderr)
        return None
    return issues


def issues_by_problem(issues):
    """Open sync issues grouped by problem number (a string), oldest first."""
    out = {}
    for issue in sorted(issues, key=lambda i: i["number"]):
        match = ISSUE_TITLE_RE.match(issue["title"])
        if match:
            out.setdefault(match.group(1), []).append(issue)
    return out


def plan_issue_sync(mismatches, issues):
    """Decide what to do with the sync issues for the current mismatches.

    Returns `(to_create, to_edit, duplicates)`:
    - `to_create`: mismatches with no open issue.
    - `to_edit`: `(issue, mismatch)` pairs for the oldest open issue of a problem whose title
      or managed labels no longer match the computed sides.
    - `duplicates`: `(issue number, kept issue number)` pairs for every newer open issue of
      a problem that still mismatches.

    Kept separate from the `gh` calls so it can be tested.
    """
    grouped = issues_by_problem(issues)
    to_create, to_edit, duplicates = [], [], []
    for m in mismatches:
        existing = grouped.get(str(m["number"]), [])
        if not existing:
            to_create.append(m)
            continue
        kept, *rest = existing
        # Check the labels even if the title is current. Otherwise a label left over from an
        # earlier status would never be corrected.
        if kept["title"] != issue_title(m) or any(label_changes(m, kept)):
            to_edit.append((kept, m))
        duplicates.extend((issue["number"], kept["number"]) for issue in rest)
    return to_create, to_edit, duplicates


def issue_body(m):
    num = m["number"]
    return (
        f"The status of [Erdős problem {num}]"
        f"(https://www.erdosproblems.com/{num}) "
        f"appears to have changed.\n\n"
        f"- **[This repo](http://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/{num}.lean)**: `{m['lean_status']}` "
        f"(in `FormalConjectures/ErdosProblems/{num}.lean`)\n"
        f"- **[erdosproblems.com/{num}](https://www.erdosproblems.com/{num})**: `{m['yaml_status']}`\n\n"
        f"Please verify and update the `@[category research ...]` "
        f"annotation if appropriate."
    )


def sync_issues(mismatches, issues):
    """Create, edit, and deduplicate sync issues for the current mismatches.

    Requires the `gh` CLI to be installed and GH_TOKEN to be set.
    """
    to_create, to_edit, duplicates = plan_issue_sync(mismatches, issues)

    for m in to_create:
        cmd = ["gh", "issue", "create", "--title", issue_title(m), "--body", issue_body(m)]
        for label in issue_labels(m):
            cmd.extend(["--label", label])
        subprocess.run(cmd)

    for issue, m in to_edit:
        number = issue["number"]
        retitle = issue["title"] != issue_title(m)
        to_add, to_remove = label_changes(m, issue)
        cmd = ["gh", "issue", "edit", str(number)]
        if retitle:
            cmd.extend(["--title", issue_title(m)])
        for label in to_add:
            cmd.extend(["--add-label", label])
        for label in to_remove:
            cmd.extend(["--remove-label", label])
        # Comment only after a successful edit. Otherwise the title stays stale and the
        # next hourly run posts the same comment again.
        if subprocess.run(cmd).returncode != 0:
            print(f"Failed to edit issue #{number}", file=sys.stderr)
            continue
        if not retitle:
            continue  # a label correction alone needs no comment
        subprocess.run([
            "gh", "issue", "comment", str(number),
            "--body",
            f"The mismatch has changed. This repository now reads `{m['lean_status']}` "
            f"and erdosproblems.com reads `{m['yaml_status']}`. Title updated automatically.",
        ])

    for number, kept in duplicates:
        subprocess.run([
            "gh", "issue", "close", str(number),
            "--reason", "not planned",
            "--comment", f"Duplicate of #{kept}. Closed automatically.",
        ])


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


def close_resolved_issues(mismatches, issues):
    """Close open sync issues whose mismatch has gone away.

    `mismatches` is everything still disagreeing, so any other open issue under the label has
    been overtaken by a merge.
    """
    # `find_mismatches` keys problems by string, so compare as strings.
    still_open = {str(m["number"]) for m in mismatches}
    known = classifiable()
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
        issues = list_sync_issues()
        if issues is None:
            # Without the list, every mismatch looks new and every issue looks stale.
            print("Not creating, editing, or closing any issue", file=sys.stderr)
        else:
            sync_issues(mismatches, issues)
            # Runs even when nothing mismatches, which is exactly when there is most to close.
            close_resolved_issues(mismatches, issues)

    return 1 if mismatches else 0


if __name__ == "__main__":
    sys.exit(main())
