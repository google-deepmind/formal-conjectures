/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 14

*Reference:* [erdosproblems.com/14](https://www.erdosproblems.com/14)
-/

namespace Erdos14

open Asymptotics Filter

abbrev allUniqueSums (A : Set ℕ) : Set ℕ :=
  { n | ∃! (a : ℕ × ℕ), a.1 ≤ a.2 ∧ a.1 ∈ A ∧ a.2 ∈ A ∧ a.1 + a.2 = n }

/--
The number of integers in $\{1,\ldots,N\}$ which are not representable in exactly one way
as the sum of two elements from $A$ (either because they are not representable at all, or
because they are representable in more than one way).
-/
noncomputable def nonUniqueSumCount (A : Set ℕ) (N : ℕ) : ℝ :=
  ((Set.Icc 1 N) \ (allUniqueSums A)).ncard

noncomputable def almostSquareRoot (ε : ℝ) (N : ℕ) : ℝ :=
  N ^ (1/2 - ε)

noncomputable def squareRoot (N : ℕ) : ℝ :=
  Real.sqrt N

/--
Let $A ⊆ \mathbb{N}$. Let $B ⊆ \mathbb{N}$ be the set of integers which are representable
in exactly one way as the sum of two elements from $A$. Is it true that for all
$\epsilon > 0$ and large $N$, $|\{1,\ldots,N\} \setminus B| \gg_\epsilon N^{1/2 - \epsilon}$?
-/
@[category research open, AMS 11]
theorem erdos_14a :
    (∀ A, ∀ ε > 0, nonUniqueSumCount A ≫ almostSquareRoot ε) ↔ answer(sorry) := by sorry

/--
Is it possible that $|\{1,\ldots,N\} \setminus B| = o(N^\frac{1}{2})$?
-/
@[category research open, AMS 11]
theorem erdos_14b :
    (∃ (A : Set ℕ), IsLittleO atTop (nonUniqueSumCount A) squareRoot) ↔ answer(sorry) := by
  sorry

end Erdos14
