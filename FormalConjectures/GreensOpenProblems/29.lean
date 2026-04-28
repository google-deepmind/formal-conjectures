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

import FormalConjectures.Util.ProblemImports
import Mathlib.Combinatorics.Additive.ApproximateSubgroup

/-!
# Ben Green's Open Problem 29

*References:*
- [Ben Green's Open Problem 29](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.29)
- [Gr12] Green, Ben. "What is... an approximate group." Notices Amer. Math. Soc 59.5 (2012): 655-656.
- [Br13] Breuillard, Emmanuel, Ben Green, and Terence Tao. "Small doubling in groups."
  Erdős Centennial. Berlin, Heidelberg: Springer Berlin Heidelberg, 2013. 129-151.
- [Sa10] Sanders, Tom. "On a nonabelian Balog–Szemerédi-type lemma." Journal of the Australian
  Mathematical Society 89.1 (2010): 127-132.
- [CrSi10] Croot, Ernie, and Olof Sisask. "A probabilistic technique for finding almost-periods of
  convolutions." Geometric and functional analysis 20.6 (2010): 1367-1396.
-/

open scoped Pointwise

namespace Green29

/-- Suppose that $A$ is a $K$-approximate group (not necessarily abelian). Is there $S \subset A$,
$|S| \gg K^{-O(1)} |A|$, with $S^8 \subset A^4$? -/
@[category research open, AMS 20]
theorem green_29 :
    answer(sorry) ↔
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ {G : Type*} [Group G] [DecidableEq G] (K : ℝ) (A : Finset G),
          1 ≤ K → IsApproximateSubgroup K (A : Set G) →
            ∃ S ⊆ A, C * K ^ (-c) * (A.card : ℝ) ≤ (S.card : ℝ) ∧
            S ^ 8 ⊆ A ^ 4 := by
  sorry

/-- Such a conclusion is known with $|S| \gg_K |A|$ [Br13 Problem 6.5, CrSi10, Sa10]. -/
@[category research solved, AMS 20]
theorem green_29.variant :
    ∀ K : ℝ, 1 ≤ K →
      ∃ c : ℝ, 0 < c ∧ -- Allow c to depend on K.
        ∀ {G : Type*} [Group G] [DecidableEq G] (A : Finset G),
          IsApproximateSubgroup K (A : Set G) →
            ∃ S : Finset G, -- No S ⊆ A requirement in this variant.
              c * (A.card : ℝ) ≤ (S.card : ℝ) ∧
              S ^ 8 ⊆ A ^ 4 := by
  sorry

end Green29
