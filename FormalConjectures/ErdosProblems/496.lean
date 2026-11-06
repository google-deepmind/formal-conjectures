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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 496

*References:*
- [erdosproblems.com/496](https://www.erdosproblems.com/496)
- [Ma89] Margulis, G. A., Discrete subgroups and ergodic theory.
  Number theory, trace formulas and discrete groups (Oslo, 1987) (1989), 377–398.
-/

@[expose] public section

namespace Erdos496

/--
Let $\alpha \in \mathbb{R}$ be irrational and $\epsilon>0$. Are there positive integers
$x,y,z$ such that $\lvert x^2+y^2-z^2\alpha\rvert <\epsilon$?

This is true, and was proved by Margulis [Ma89].
We require $\alpha>0$, so the quadratic form is indefinite. Without this restriction,
nonpositive coefficients give values at least $2$ for positive $x,y$.
-/
@[category research solved, AMS 11]
theorem erdos_496 : answer(True) ↔
    ∀ α : ℝ, 0 < α → Irrational α → ∀ ε : ℝ, 0 < ε →
      ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
        |(x : ℝ) ^ 2 + (y : ℝ) ^ 2 - (z : ℝ) ^ 2 * α| < ε := by sorry

/--
Without the restriction $\alpha>0$, the displayed question has a negative answer:
$\alpha=-\sqrt{2}$ and $\epsilon=1$ give a counterexample.
-/
@[category textbook, AMS 11]
theorem erdos_496.variants.without_positive_coefficient : answer(False) ↔
    ∀ α : ℝ, Irrational α → ∀ ε : ℝ, 0 < ε →
      ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
        |(x : ℝ) ^ 2 + (y : ℝ) ^ 2 - (z : ℝ) ^ 2 * α| < ε := by
  constructor
  · intro h
    exact h.elim
  · intro h
    obtain ⟨x, y, z, hx, hy, _, hsmall⟩ :=
      h (-Real.sqrt 2) irrational_sqrt_two.neg 1 (by norm_num)
    have hx' : (1 : ℝ) ≤ x := by exact_mod_cast hx
    have hy' : (1 : ℝ) ≤ y := by exact_mod_cast hy
    have hterm : (z : ℝ) ^ 2 * (-Real.sqrt 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (neg_nonpos.mpr (Real.sqrt_nonneg _))
    have habs := le_abs_self ((x : ℝ) ^ 2 + (y : ℝ) ^ 2 - (z : ℝ) ^ 2 * (-Real.sqrt 2))
    nlinarith [sq_nonneg ((x : ℝ) - 1), sq_nonneg ((y : ℝ) - 1)]

end Erdos496
