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
# Partial minimum branching-program size

Glinskih–Riazanov, *Partial Minimum Branching Program Size Problem Is ETH-Hard*,
ITCS 2025, pp. 54:1–54:22; definitions in §2, pp. 54:5–54:6:
https://doi.org/10.4230/LIPIcs.ITCS.2025.54.

The input is a complete partial truth table and a binary size bound.
Witnesses are unrestricted deterministic Boolean branching programs, with one
source and two sinks. Size counts all nodes, including both sinks. The graph
convention requires every non-root node to have an incoming edge; unused sinks
are not permitted. Consequently the zero-variable case has no witnesses.
Repeated queries are allowed; no read-once, ordering, or width bound is imposed.
-/

namespace GlinskihRiazanov2025

/-- Does partial Minimum Branching Program Size admit a deterministic
polynomial-time decider, using the full partial table as input? -/
@[category research open, AMS 3 68]
theorem partialMinimumBranchingProgram_polytime : answer(sorry) ↔
    ComplexityTheory.HasPolyTimeDecider TruthTableMinimization.PartialMinimumBranchingProgram := by
  sorry

end GlinskihRiazanov2025
