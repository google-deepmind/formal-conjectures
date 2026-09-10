/-
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
-/
import FormalConjecturesUtil

/-!
# Polynomial-time End-of-Line search

Ghentiyala–Li, *Hierarchies within TFNP: building blocks and collapses*,
ECCC TR25-123 revision1, Definition2.8, printed p.8:
https://eccc.weizmann.ac.il/report/2025/123/revision/1/download.

The source defines the canonical PPAD search problem. This asks for a uniform
solver for its encoded circuit instances, not a traversal of the implicit graph.
-/

namespace GhentiyalaLi2025

/-- Does End-of-Line admit a deterministic polynomial-time solver? Both a broken
successor-predecessor connection and a nonzero vertex with a broken
predecessor-successor connection are allowed answers. -/
@[category research open, AMS 3 68]
theorem endOfLine_polytime : answer(sorry) ↔
    ComplexityTheory.HasPolyTimeSolver TotalSearch.EndOfLinePromise
      TotalSearch.EndOfLineSolution := by
  sorry

end GhentiyalaLi2025
