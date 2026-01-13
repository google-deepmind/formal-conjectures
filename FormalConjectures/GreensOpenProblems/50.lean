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
# Ben Green's Open Problem 50

*Reference:* [Ben Green's Open Problem 50](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.50)
-/

open Pointwise

namespace Green50

/-- `iteratedSum A n` is the sumset `A + ... + A` (n times). -/
def iteratedSum {α} [AddMonoid α] [DecidableEq α] (A : Finset α) : ℕ → Finset α
  | 0 => {0}
  | n + 1 => A + iteratedSum A n

/--
Ben Green's Open Problem 50 (Polynomial Bogolyubov conjecture).
Suppose that $A \subset \mathbb{F}_2^n$ be a set of density $\alpha$.
Does $10A$ contain a coset of some subspace of dimension at least $n - O(\log(1/\alpha))$?
-/
@[category research open, AMS 05 11]
theorem green_50 : answer(sorry) ↔
  ∃ C > 0, ∀ (n : ℕ) (α : ℝ) (A : Finset (Fin n → ZMod 2)),
    0 < α → (A.card : ℝ) = α * (2 ^ n : ℝ) →
    ∃ V : Submodule (ZMod 2) (Fin n → ZMod 2),
      (n : ℝ) - C * Real.log (1 / α) ≤ (Module.finrank (ZMod 2) V : ℝ) ∧
      ∃ x, ∀ v ∈ V, x + v ∈ iteratedSum A 10 := by
  sorry

end Green50
