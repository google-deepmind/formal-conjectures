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

"""How long the adapter waits for anything it does not control.

Every subprocess here is bounded, and the bounds are stated once. They live
in their own module because the four callers — source reading, the importer,
the generator plumbing and the target compile — otherwise have no reason to
import one another, and a shared constant is not a reason to grow the
dependency graph.
"""

# A Lean run that has not answered by now is stuck, not slow: a cold run
# imports Mathlib and may build the extractor first, and that is minutes.
# A hang should end the run, not the day.
LEAN_TIMEOUT_SECONDS = 1800

# Each extra pair in a batch shares one environment, so it costs elaboration
# but not another import.
BATCH_TIMEOUT_PER_PAIR_SECONDS = 30

# Git here is local and reads the index; a minute means a stuck lock file.
GIT_TIMEOUT_SECONDS = 60
