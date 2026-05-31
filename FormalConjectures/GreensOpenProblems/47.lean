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
# Green's Open Problem 47

*References:*
- [Gr24] [Ben Green's 100 Open Problems](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.47)
-/

open Filter

namespace Green47

/-- A map $\phi : \mathbb{Q} \to \mathbb{Q}$ is quadratic if it is of the form $\phi(x) = ax^2 + bx + c$. -/
def IsQuadratic (f : ℚ → ℚ) : Prop :=
  ∃ a b c : ℚ, a ≠ 0 ∧ ∀ x, f x = a * x^2 + b * x + c

/--
Suppose that a large sieve process leaves a set of quadratic size. Is that set quadratic?

The following very particular instance is probably the simplest [Gr24]:
Suppose that $A \subset \mathbb{N}$ is a set with the property that
$|A \pmod p| \leqslant \frac{1}{2}(p + 1)$ for all sufficiently large $p$.
Is it true that either $|A \cap [X]| \ll X^{1/2} / \log^{100} X$, or $A$ is contained in the
image of $\mathbb{Z}$ under a quadratic map $\phi : \mathbb{Q} \to \mathbb{Q}$?
-/
@[category research open, AMS 11]
theorem green_47 :
    answer(sorry) ↔ ∀ A : Set ℕ,
      (∀ᶠ p in atTop, Nat.Prime p → Set.ncard (Set.image (fun a : ℕ => (a : ZMod p)) A) ≤ (p + 1) / 2) →
      (fun X : ℕ => ((A ∩ Set.Iic X).ncard : ℝ)) =O[atTop] (fun X : ℕ => (X : ℝ) ^ (1/2 : ℝ) / (Real.log (X : ℝ)) ^ 100)
      ∨ (∃ ϕ : ℚ → ℚ, IsQuadratic ϕ ∧ ∀ a ∈ A, ∃ z : ℤ, (a : ℚ) = ϕ z) := by
  sorry

end Green47
