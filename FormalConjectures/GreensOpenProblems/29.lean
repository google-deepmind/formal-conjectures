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

/-!
# Ben Green's Open Problem 29

*References:*
* [Ben Green's Open Problem 29](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.29)
-/

open Finset Real
open scoped Pointwise

namespace Green29

/-- A subset `A` of a group `G` is a `K`-approximate group if it is symmetric, contains the identity,
and there exists a set `X` of size at most `K` such that `A * A ⊆ X * A`. -/
def IsApproximateGroup {G : Type*} [Group G] [DecidableEq G] (K : ℝ) (A : Finset G) : Prop :=
  (1 : G) ∈ A ∧ A⁻¹ = A ∧ ∃ X : Finset G, (X.card : ℝ) ≤ K ∧ A * A ⊆ X * A

/-- Suppose that $A$ is a $K$-approximate group (not necessarily abelian). Is there $S \subset A$,
$|S| \gg K^{-O(1)} |A|$, with $S^8 \subset A^4$? -/
@[category research open, AMS 20]
theorem green_29 :
    answer(sorry) ↔
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ {G : Type*} [Group G] [DecidableEq G] (K : ℝ) (A : Finset G),
          IsApproximateGroup K A →
            ∃ S ⊆ A, C * K ^ (-c) * (A.card : ℝ) ≤ (S.card : ℝ) ∧
            S ^ 8 ⊆ A ^ 4 := by
  sorry

end Green29
