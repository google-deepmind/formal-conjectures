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
# Five finite-set formulations of P versus NP

These are the conjectured nonexistence of polynomial-time deciders for five classical
NP-complete problems, with explicit finite families and binary element names.
Karp's completeness theorem and Theorem 3 explain their relation to $P \ne NP$.
The completeness reductions themselves are not proved in this file.

*Reference:* Richard M. Karp, *Reducibility among Combinatorial Problems*, in
*Complexity of Computer Computations* (1972), pp. 85–103,
https://doi.org/10.1007/978-1-4684-2001-2_9.
See §4, Theorem 3 (p. 93), and Main Theorem items 4, 6, 14, 15, 17 (pp. 94–95).
-/

namespace Karp1972

open ComplexityTheory Computability.FiniteSetProblems

/-- No polynomial-time decider for SET PACKING, with a positive requested number of
pairwise disjoint sets (item 4, p. 94). -/
@[category research open, AMS 5 68]
theorem setPacking_not_polytime : ¬ HasPolyTimeDecider SetPacking := by
  sorry

/-- No polynomial-time decider for SET COVERING, with a positive upper bound on the
number of selected sets (item 6, p. 94). -/
@[category research open, AMS 5 68]
theorem setCovering_not_polytime : ¬ HasPolyTimeDecider SetCovering := by
  sorry

/-- No polynomial-time decider for EXACT COVER of an explicit ambient universe
(item 14, p. 95). -/
@[category research open, AMS 5 68]
theorem exactCover_not_polytime : ¬ HasPolyTimeDecider ExactCover := by
  sorry

/-- No polynomial-time decider for HITTING SET in Karp's exact sense: the witness
intersects each set in exactly one element (item 15, p. 95). -/
@[category research open, AMS 5 68]
theorem exactHitting_not_polytime : ¬ HasPolyTimeDecider ExactHitting := by
  sorry

/-- No polynomial-time decider for 3-DIMENSIONAL MATCHING of size equal to the
explicit ambient universe (item 17, p. 95). -/
@[category research open, AMS 5 68]
theorem threeDimensionalMatching_not_polytime :
    ¬ HasPolyTimeDecider ThreeDimensionalMatching := by
  sorry

end Karp1972
