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

"""The known-failures ledger: `comparator/known_failures.toml` and its loader.

Both gates read the ledger — the source-side set run and the target-side
compile — and each matches it exactly: an unexpected failure and a silently
fixed one both fail. The loader lives here so neither command has to import
the other to read the format.
"""

import tomllib

def load_known_failures(path):
    """The recorded failures, `{declaration: {stage, reason}}`."""
    with open(path, "rb") as handle:
        data = tomllib.load(handle)
    failures = {}
    for entry in data.get("failure", []):
        for field in ("declaration", "stage", "reason"):
            if field not in entry:
                raise SystemExit(f"{path}: a failure entry has no `{field}`")
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
        failures[entry["declaration"]] = entry
    return failures
