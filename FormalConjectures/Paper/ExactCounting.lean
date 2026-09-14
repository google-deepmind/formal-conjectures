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
# Exact counting and polynomial time

*References:*
* Valiant, *The Complexity of Computing the Permanent* (1979), §2,
  Theorem 1 and Lemmas 3.1–3.3, pp. 189–193,
  https://doi.org/10.1016/0304-3975(79)90044-6.
-/

namespace Valiant1979

/-- **Exact #SAT counting** (Valiant, §§2–3) is not computable in deterministic
polynomial bit-time. Input: an explicit CNF formula with binary variable names;
output: the exact binary number of satisfying assignments to precisely the names
occurring in the formula. Repeated literals and clauses are allowed. Empty CNF
has count one; an empty clause gives count zero. This counting lower bound follows
from $P\ne NP$, since positivity of the count decides SAT; the converse is not asserted. -/
@[category research open, AMS 3 68]
theorem modelCount_not_polytime : ¬ ComplexityTheory.IsPolyTime ExactCounting.modelCount := by
  sorry

/-- **Exact 0–1 permanent computation** (Valiant, Theorem 1) is not possible in
deterministic polynomial bit-time. Input: an explicit Boolean row matrix; output:
the permanent as an exact binary natural number. Ragged matrices return zero;
the empty square matrix has permanent one. This is a #P-complete counting task,
so $P\ne NP$ implies the lower bound, without an asserted converse. Neither
approximation nor nonuniform arithmetic-circuit size is the target. -/
@[category research open, AMS 15 68]
theorem permanent_not_polytime : ¬ ComplexityTheory.IsPolyTime ExactCounting.permanent := by
  sorry

end Valiant1979
