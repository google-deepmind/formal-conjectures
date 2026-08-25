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

"""The known-failures ledger: `comparator/known_failures.toml`, its loader and its gate.

Both stages read the ledger — the source-side set run and the target-side
compile — and each matches it exactly: an unexpected failure and a silently
fixed one both fail. Format, loader and comparison live here so the two
stages cannot drift into disagreeing about what the ledger means, and so
neither command has to import the other to read it.
"""

import sys
import tomllib

KNOWN_KEYS = frozenset({"declaration", "stage", "reason", "workspace"})


def load_known_failures(path):
    """The recorded failures, `{declaration: {stage, reason}}`.

    Strict like every other boundary here: a key nothing reads is refused
    rather than carried, and a declaration recorded twice is refused rather
    than last-one-wins — a shadowed entry would quietly defeat the exact
    match the gates promise.
    """
    with open(path, "rb") as handle:
        data = tomllib.load(handle)
    failures = {}
    for entry in data.get("failure", []):
        for field in ("declaration", "stage", "reason"):
            if field not in entry:
                raise SystemExit(f"{path}: a failure entry has no `{field}`")
        unknown = sorted(set(entry) - KNOWN_KEYS)
        if unknown:
            raise SystemExit(
                f"{path}: {entry['declaration']} has unknown keys: "
                f"{', '.join(unknown)}"
            )
        if entry["stage"] not in ("source", "target"):
            raise SystemExit(
                f"{path}: {entry['declaration']} has stage {entry['stage']!r}; "
                "expected source or target"
            )
        if entry["stage"] == "target" and "workspace" not in entry:
            raise SystemExit(
                f"{path}: {entry['declaration']} is a target failure without a "
                "`workspace`; the target gate matches by workspace id"
            )
        if entry["declaration"] in failures:
            raise SystemExit(
                f"{path}: {entry['declaration']} is recorded twice"
            )
        failures[entry["declaration"]] = entry
    return failures


def expected_failures(recorded, stage, key):
    """The names the ledger expects to fail at `stage`, read from `key`."""
    return {entry[key] for entry in recorded.values() if entry["stage"] == stage}


def gate(recorded, actual, stage, key):
    """Whether the observed failures are exactly the recorded ones.

    Both directions fail. An unexpected failure is the obvious one; a
    recorded failure that no longer happens is the one a gate without this
    check would never mention, and a ledger nobody prunes stops describing
    the run it guards.
    """
    expected = expected_failures(recorded, stage, key)
    unexpected = sorted(set(actual) - expected)
    fixed = sorted(expected - set(actual))
    for name in unexpected:
        print(f"unexpected {stage} failure: {name}", file=sys.stderr)
    for name in fixed:
        print(
            f"{name} is recorded as a known {stage} failure but did not fail; "
            "remove it from the record",
            file=sys.stderr,
        )
    return not (unexpected or fixed)
