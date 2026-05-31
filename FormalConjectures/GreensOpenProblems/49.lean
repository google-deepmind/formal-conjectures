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

/--
Suppose that $A \subset \mathbb{F}_2^n$ is a set with $|A + A| \leq K|A|$. Is it true that $A$
is covered by $K^{O(1)}$ translates of a subspace of size $\leq |A|$?
-/
@[category research solved, AMS 5 11]
theorem green_49 : answer(True) ↔
    ∃ C > (0 : ℝ), ∀ n : ℕ, ∀ A : Finset (Fin n → ZMod 2), A.Nonempty →
    ∀ K : ℝ, 1 ≤ K → ((#(A + A)) : ℝ) ≤ K * (#A : ℝ) →
    ∃ (W : Submodule (ZMod 2) (Fin n → ZMod 2)) (T : Finset (Fin n → ZMod 2)),
      Nat.card W ≤ #A ∧
      (#T : ℝ) ≤ K ^ C ∧
      (A : Set (Fin n → ZMod 2)) ⊆ (T : Set (Fin n → ZMod 2)) + (W : Set (Fin n → ZMod 2)) := by
  sorry

end Green49
