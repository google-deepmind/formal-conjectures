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
# Five satisfiability formulations of P versus NP

These statements conjecture the nonexistence of deterministic polynomial-time deciders
for ordinary 3-SAT and the signed and positive versions of one-in-three and not-all-equal
3-SAT. Formulas preserve literal occurrences and use binary variable names.

Schaefer's dichotomy theorem and its examples establish the classical NP-completeness
background; these reductions and the equivalence to $P \ne NP$ are not formalized here.

*References:*
- Thomas J. Schaefer, *The Complexity of Satisfiability Problems*, STOC (1978), pp. 216–226,
  https://doi.org/10.1145/800133.804350. See the relation framework on p. 216, Theorem 2.1
  on p. 217, and the rank-three relations $R_5$ and $R_6$ on p. 218.
- Richard M. Karp, *Reducibility among Combinatorial Problems* (1972), item 11, p. 95,
  https://doi.org/10.1007/978-1-4684-2001-2_9, for at-most-three ordinary clauses.
- Md. Manzurul Hasan, Debajyoti Mondal, and Md. Saidur Rahman,
  *Positive Planar Satisfiability Problems under 3-Connectivity Constraints* (2021),
  https://arxiv.org/abs/2108.12500, §1, pp. 1–2, for the signed/positive terminology
  and completeness background. No planarity restriction is imposed here.
-/

namespace Schaefer1978

open ComplexityTheory Computability.BooleanSatisfiability

/-- No polynomial-time decider for ordinary 3-SAT with at most three signed literals
per clause (Karp, item 11; Schaefer, p. 216). -/
@[category research open, AMS 3 68]
theorem threeSat_not_polytime : ¬ HasPolyTimeDecider ThreeSat := by
  sorry

/-- No polynomial-time decider for exactly-one-in-three SAT with signed literals.
Each clause has exactly three occurrences; negations and repetitions are allowed. -/
@[category research open, AMS 3 68]
theorem oneInThree_not_polytime : ¬ HasPolyTimeDecider OneInThree := by
  sorry

/-- No polynomial-time decider for positive one-in-three SAT, using Schaefer's
rank-three relation $R_6$ (pp. 216, 218), including repeated variable arguments. -/
@[category research open, AMS 3 68]
theorem positiveOneInThree_not_polytime : ¬ HasPolyTimeDecider PositiveOneInThree := by
  sorry

/-- No polynomial-time decider for not-all-equal 3-SAT with signed literals.
Each three-occurrence clause must have both a true and a false literal. -/
@[category research open, AMS 3 68]
theorem notAllEqual_not_polytime : ¬ HasPolyTimeDecider NotAllEqual := by
  sorry

/-- No polynomial-time decider for positive not-all-equal 3-SAT, using Schaefer's
rank-three relation $R_5$ (p. 218), including repeated variable arguments. -/
@[category research open, AMS 3 68]
theorem positiveNotAllEqual_not_polytime : ¬ HasPolyTimeDecider PositiveNotAllEqual := by
  sorry

end Schaefer1978
