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

import Mathlib

/-!
# Abstract Feshbach core

Two Hilbert-space facts behind the Feshbach certificates, with no trace-class theory.

* `inner_orth_le`: if `w ⊥ U` then `‖⟪w, x⟫‖ ≤ ‖w‖ · ‖x − P_U x‖`.  Integrated against a slack
  weight this bounds the slack form on the complement by `‖w‖² · ∫ s ‖e_t − P e_t‖²`.
* `feshbach_lower`: for a quadratic form split as `a(v) + 2 Re b(v,w) + q(w)` with
  `q(w) ≥ c‖w‖²`, `|b(v,w)|² ≤ β(v)‖w‖²` and `μ < c`,
  `a(v) + 2 Re b + q(w) − μ(‖v‖² + ‖w‖²) ≥ a(v) − μ‖v‖² − β(v)/(c − μ)`.
  Positivity of the right side on the finite block (a Schur matrix) gives the full bound.

AUTHORITY_EFFECT = NONE.
-/

set_option autoImplicit false

namespace AEGIS.RHFeshbachCoreV1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

open scoped InnerProductSpace

theorem inner_orth_le (U : Submodule ℂ E) [U.HasOrthogonalProjection] (w x : E)
    (hw : w ∈ Uᗮ) : ‖⟪w, x⟫_ℂ‖ ≤ ‖w‖ * ‖x - U.starProjection x‖ := by
  have hPx : U.starProjection x ∈ U := Submodule.starProjection_apply_mem U x
  have h0 : ⟪w, U.starProjection x⟫_ℂ = 0 := by
    have := (Submodule.mem_orthogonal' U w).mp hw _ hPx
    exact this
  have e : ⟪w, x⟫_ℂ = ⟪w, x - U.starProjection x⟫_ℂ := by
    rw [inner_sub_right, h0, sub_zero]
  rw [e]
  exact norm_inner_le_norm _ _

/-- The scalar Feshbach step. -/
theorem feshbach_lower (a re_b q nv nw β c μ : ℝ) (hnw : 0 ≤ nw) (hq : c * nw ^ 2 ≤ q)
    (hb : re_b ^ 2 ≤ β * nw ^ 2) (hβ : 0 ≤ β) (hμc : μ < c) :
    a - μ * nv ^ 2 - β / (c - μ) ≤ a + 2 * re_b + q - μ * (nv ^ 2 + nw ^ 2) := by
  have hcμ : 0 < c - μ := by linarith
  have hrb : -(Real.sqrt β * nw) ≤ re_b := by
    have h1 : |re_b| ≤ Real.sqrt β * nw := by
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq hnw, ← Real.sqrt_mul hβ]
      exact Real.sqrt_le_sqrt hb
    linarith [neg_abs_le re_b]
  -- (c-μ) nw² - 2√β nw + β/(c-μ) = (√(c-μ) nw - √β/√(c-μ))² ≥ 0
  have hsq : 0 ≤ (c - μ) * nw ^ 2 - 2 * (Real.sqrt β * nw) + β / (c - μ) := by
    have hs := Real.sq_sqrt hβ
    have key : (c - μ) * nw ^ 2 - 2 * (Real.sqrt β * nw) + β / (c - μ) =
        ((c - μ) * nw - Real.sqrt β) ^ 2 / (c - μ) := by
      field_simp
      ring_nf
      rw [hs]
    rw [key]; positivity
  nlinarith

end AEGIS.RHFeshbachCoreV1

#print axioms AEGIS.RHFeshbachCoreV1.inner_orth_le
#print axioms AEGIS.RHFeshbachCoreV1.feshbach_lower
