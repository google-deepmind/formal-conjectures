#!/usr/bin/env python3
"""Generate FC100Open.lean and FC100Solved.lean subset files.

Randomly samples 100 problems each from extracted_names.json:
  - FC100Open:   drawn uniformly at random from `category research open` problems
  - FC100Solved: drawn uniformly at random from all other categories
    (research solved, test, API, undergraduate, high_school, graduate)

All problems are eligible for sampling (no filtering). A custom `decl_name%`
elaborator resolves each theorem identifier to verify the declaration exists
at compile time, and stores the result as a `Lean.Name`. This avoids the
type-elaboration issues that `type_of%` has with implicit arguments,
typeclass instances, and universe polymorphism.

Usage:
    cd <repo-root>
    python3 FormalConjectures/Subsets/generate_fc100.py
"""

import json
import random
import os
import sys
from collections import Counter

SEED = 42
SAMPLE_SIZE = 100

COPYRIGHT = """/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/"""

def generate_lean_file(
    sample: list[dict],
    namespace: str,
    description: str,
) -> str:
    """Generate a Lean file with a `problems : List Name` definition."""
    modules = sorted(set(p["module"] for p in sample))
    imports = "\n".join(f"import {m}" for m in modules)

    entries = []
    for i, p in enumerate(sample):
        comma = "," if i < len(sample) - 1 else ""
        entries.append(f"  decl_name% {p['theorem']}{comma}")
    entries_str = "\n".join(entries)

    return (
        f"{COPYRIGHT}\n"
        f"\n"
        f"import FormalConjectures.Util.DeclName\n"
        f"{imports}\n"
        f"\n"
        f"/-!\n"
        f"# {description}\n"
        f"-/\n"
        f"\n"
        f"namespace Subsets.{namespace}\n"
        f"\n"
        f"open Lean in\n"
        f"def problems : List Name := [\n"
        f"{entries_str}\n"
        f"]\n"
        f"\n"
        f"end Subsets.{namespace}\n"
    )


def main():
    # Locate extracted_names.json relative to repo root.
    repo_root = os.path.dirname(
        os.path.dirname(os.path.abspath(__file__))
    )
    json_path = os.path.join(repo_root, "extracted_names.json")

    if not os.path.exists(json_path):
        print(f"Error: {json_path} not found. Run from the repo root.", file=sys.stderr)
        sys.exit(1)

    with open(json_path) as f:
        data = json.load(f)

    problems = data["problems"]

    # Partition into open vs non-open — no filtering, sample from all.
    open_problems = [p for p in problems if p["category"] == "research open"]
    other_problems = [p for p in problems if p["category"] != "research open"]

    print(f"Total problems:  {len(problems)}")
    print(f"  research open: {len(open_problems)}")
    print(f"  other:         {len(other_problems)}")

    if len(open_problems) < SAMPLE_SIZE:
        print(
            f"Error: not enough open problems ({len(open_problems)} < {SAMPLE_SIZE})",
            file=sys.stderr,
        )
        sys.exit(1)
    if len(other_problems) < SAMPLE_SIZE:
        print(
            f"Error: not enough other problems ({len(other_problems)} < {SAMPLE_SIZE})",
            file=sys.stderr,
        )
        sys.exit(1)

    random.seed(SEED)
    open_sample = random.sample(open_problems, SAMPLE_SIZE)
    other_sample = random.sample(other_problems, SAMPLE_SIZE)

    # Generate files.
    open_content = generate_lean_file(
        open_sample,
        "FC100Open",
        "FC100Open\n\nA random subset of 100 open research problems, drawn uniformly "
        "at random\nfrom all problems with the `category research open` tag.",
    )

    open_content += """
open Lean Meta ProblemAttributes in
#eval verifyCategoryCounts Subsets.FC100Open.problems [
  ("research open", 100)
]
"""
    solved_content = generate_lean_file(
        other_sample,
        "FC100Solved",
        "FC100Solved\n\nA random subset of 100 non-open problems, drawn uniformly at "
        "random\nfrom all problems without the `category research open` tag\n"
        "(solved, test, API, etc.).",
    )

    counts = Counter(p["category"] for p in other_sample)
    pairs = [f'  ("{cat}", {count})' for cat, count in counts.items()]
    pairs_str = ",\n".join(pairs)

    solved_content += f"""
open Lean Meta ProblemAttributes in
#eval verifyCategoryCounts Subsets.FC100Solved.problems [
{pairs_str}
]
"""

    out_dir = os.path.join(repo_root, "FormalConjectures", "Subsets")
    open_path = os.path.join(out_dir, "FC100Open.lean")
    solved_path = os.path.join(out_dir, "FC100Solved.lean")

    with open(open_path, "w") as f:
        f.write(open_content)
    with open(solved_path, "w") as f:
        f.write(solved_content)

    open_modules = len(set(p["module"] for p in open_sample))
    solved_modules = len(set(p["module"] for p in other_sample))
    print(f"\nGenerated:")
    print(f"  {open_path}   ({SAMPLE_SIZE} problems from {open_modules} modules)")
    print(f"  {solved_path} ({SAMPLE_SIZE} problems from {solved_modules} modules)")


if __name__ == "__main__":
    main()
