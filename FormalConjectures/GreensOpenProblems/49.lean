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
# Green's Open Problem 49

*Reference:* [Ben Green's Open Problems](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.49)

Suppose that $A \subset \mathbb{F}_2^n$ is a set with $|A + A| \leq K|A|$. Is it true that $A$
is covered by $K^{O(1)}$ translates of a subspace of size $\leq |A|$?
-/

open scoped Pointwise Finset

namespace Green49

/-- The vector space $\mathbb{F}_2^n$. -/
abbrev 𝔽₂ (n : ℕ) := Fin n → ZMod 2

/--
Suppose that $A \subset \mathbb{F}_2^n$ is a set with $|A + A| \leq K|A|$. Is it true that $A$
is covered by $K^{O(1)}$ translates of a subspace of size $\leq |A|$?
-/
@[category research solved, AMS 5 11]
theorem green_49 : answer(True) ↔
    ∃ C > (0 : ℝ),
      ∀ n : ℕ, ∀ A : Finset (𝔽₂ n), A.Nonempty →
      ∀ K : ℝ, 1 ≤ K → ((#(A + A)) : ℝ) ≤ K * (#A : ℝ) →
        ∃ (W : Submodule (ZMod 2) (𝔽₂ n)) (T : Finset (𝔽₂ n)),
          Nat.card W ≤ #A ∧
          (#T : ℝ) ≤ K ^ C ∧
          (A : Set (𝔽₂ n)) ⊆ (T : Set (𝔽₂ n)) + (W : Set (𝔽₂ n)) := by
  sorry

end Green49
