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

public import FormalConjecturesForMathlib.Data.Real.Constants
public import Mathlib.Analysis.PSeries

/-!
# Dirichlet beta values at natural exponents

This file defines the alternating odd-reciprocal series `dirichletBetaNat` representing
$\beta(s) = \sum_{n=0}^{\infty} (-1)^n / (2n + 1)^s$ for integer arguments $s \ge 2$.
-/

@[expose] public section

/-- Alternating odd-reciprocal series $\beta(s) = \sum_{n=0}^{\infty} (-1)^n / (2n + 1)^s$ for
integer exponents $s \ge 2$ (where the series converges absolutely; for $s \in \{0, 1\}$, Lean's
`tsum` over `ℝ` returns `0` rather than the analytic values $\beta(0) = 1/2$ and
$\beta(1) = \pi/4$). -/
noncomputable def dirichletBetaNat (s : ℕ) : ℝ :=
  ∑' n : ℕ, ((-1 : ℝ) ^ n) / ((2 * n + 1 : ℝ) ^ s)

/-- The defining series of `dirichletBetaNat s` is summable whenever $s \ge 2$. -/
theorem summable_dirichletBetaNat_term {s : ℕ} (hs : 2 ≤ s) :
    Summable (fun n : ℕ => ((-1 : ℝ) ^ n) / ((2 * n + 1 : ℝ) ^ s)) := by
  apply Summable.of_norm_bounded (g := fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 2))
  · exact (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  · intro n
    rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_of_nonneg (by positivity)]
    apply one_div_le_one_div_of_le (by positivity)
    push_cast
    calc
      ((n + 1 : ℝ) ^ 2) ≤ ((2 * n + 1 : ℝ) ^ 2) := by gcongr; linarith
      _ ≤ ((2 * n + 1 : ℝ) ^ s) := pow_le_pow_right₀ (by linarith) hs

/-- At $s = 2$, `dirichletBetaNat 2` is definitionally equal to `catalanConstant`. -/
theorem dirichletBetaNat_two_eq_catalanConstant :
    dirichletBetaNat 2 = catalanConstant :=
  rfl
