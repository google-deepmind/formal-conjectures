#!/usr/bin/env python3
# Copyright 2026 The Formal Conjectures Authors.
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

"""Prioritize changed problem files before the comprehensive PR build.

Use the checked-out PR merge commit and its first parent. This is an early
failure check, never a substitute for the full library, problem, and test build.
"""

import argparse
from pathlib import Path
import shlex
import subprocess
import sys

MAX_FILES = 20


def changed_problems(base, head):
    result = subprocess.run(
        ["git", "diff", "--name-only", "-z", "--no-renames", "--diff-filter=AM",
         base, head, "--", "FormalConjectures/"],
        check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )
    # With rename detection off, a renamed file is selected at its new path.
    # Lake resolves paths itself, including numeric and quoted module names.
    return sorted(path for path in result.stdout.decode("utf-8").split("\0")
                  if path.endswith(".lean") and path != "FormalConjectures/All.lean")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", default="HEAD^1", help="PR merge commit's first parent")
    parser.add_argument("--head", default="HEAD", help="Checked-out PR merge commit")
    parser.add_argument("--summary", required=True, help="Build wrapper's output JSON file")
    args = parser.parse_args(argv)
    try:
        paths = changed_problems(args.base, args.head)
    except (subprocess.CalledProcessError, UnicodeError):
        print("Cannot determine changed problem files; continuing to the full build.", flush=True)
        return 0
    if not paths:
        print("No added or modified problem files; continuing to the full build.", flush=True)
        return 0
    if len(paths) > MAX_FILES:
        print(f"{len(paths)} changed problem files exceed the {MAX_FILES}-file early-check limit; "
              "continuing to the full build.", flush=True)
        return 0
    print("Checking changed problem files first: " + shlex.join(paths), flush=True)
    wrapper = Path(__file__).with_name("lake-build-wrapper.py")
    # One Lake invocation, in the same workspace and build context as the full
    # build. Do not catch its failure: syntax, elaboration, and warnings must fail.
    return subprocess.run([sys.executable, str(wrapper), args.summary,
                           "lake", "--wfail", "build", *paths]).returncode


if __name__ == "__main__":
    raise SystemExit(main())
