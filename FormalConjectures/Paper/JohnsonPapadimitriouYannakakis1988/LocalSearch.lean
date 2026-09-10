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
# Circuit-FLIP has no polynomial-time solver

*References:*
* Johnson, Papadimitriou and Yannakakis, *How Easy Is Local Search?* (1988),
  §3, Theorem 1, pp. 86–87, https://doi.org/10.1016/0022-0000(88)90046-3.
-/

namespace JohnsonPapadimitriouYannakakis1988

/-- **Circuit-FLIP** (Johnson–Papadimitriou–Yannakakis, §3) has no deterministic
polynomial-time solver. Input: a valid explicit AND/OR/NOT circuit with unary
input arity and binary references. Output: an input bit vector whose output cost
is no greater than at any one-bit flip. Cost is twice the little-endian output
value, following the source's one-based powers of two; ties are allowed. Every
valid circuit is included, even with zero input or output bits. The solver must
be total and polynomial-time, correct on valid circuits, and may return any local
minimum rather than a prescribed improvement-path endpoint. This PLS lower bound
implies $P\ne NP$; the converse is unknown. -/
@[category research open, AMS 68 90]
theorem circuitFlip_not_polytime : ¬
    ComplexityTheory.HasPolyTimeSolver EncodedBooleanCircuit.Valid TotalSearch.FlipSolution := by
  sorry

end JohnsonPapadimitriouYannakakis1988
