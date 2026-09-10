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
# Polynomial-time Circuit-FLIP search

Johnson, Papadimitriou and Yannakakis, *How Easy Is Local Search?* (1988),
§3, Theorem1, pp.86–87, https://doi.org/10.1016/0022-0000(88)90046-3.
The source proves FLIP PLS-complete. The question here is about finding any
local optimum, not following the standard improvement algorithm to its endpoint.
-/

namespace JohnsonPapadimitriouYannakakis1988

/-- Can a deterministic polynomial-time algorithm find a local minimum of the
binary-valued output of any valid Boolean circuit, with one input-bit flips
as the neighborhood? -/
@[category research open, AMS 68 90]
theorem circuitFlip_polytime : answer(sorry) ↔
    ComplexityTheory.HasPolyTimeSolver EncodedBooleanCircuit.Valid TotalSearch.FlipSolution := by
  sorry

end JohnsonPapadimitriouYannakakis1988
