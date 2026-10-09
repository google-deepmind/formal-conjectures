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

import ZeroCountingMellinSummabilityV1
import Lc.LiCriterion.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Tactic

/-!
AEGIS Ω — public zero-carrier equivalence and reflection multiplicity bridge V10.

The existing counting/summability lane already contained the mathematical map
from the AEGIS nontrivial-zeta-zero carrier to the provider's
`LiCriterion.NontrivialZero`, but that map was private.  This module exposes
the actual equivalence and proves multiplicity preservation under both the
carrier identification and the provider involution `rho ↦ 1-rho`.

AUTHORITY_EFFECT = NONE.
-/

open Complex

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilZeroCarrierBridgeV10

/-- The AEGIS zero carrier and the pinned LiCriterion carrier encode exactly
the same nontrivial zeta zeros. -/
noncomputable def aegisLiNontrivialZeroEquivV10 :
    RiemannNontrivialZeroIndexV2 ≃ LiCriterion.NontrivialZero where
  toFun rho := by
    have hstrip :=
      riemann_zeta_nontrivial_zero_critical_strip_v1 rho.2.1 rho.2.2
    exact ⟨rho.1, rho.2.1, hstrip.1, hstrip.2⟩
  invFun rho := by
    refine ⟨rho.1, rho.2.1, ?_⟩
    intro htriv
    rcases htriv with ⟨n, hn⟩
    have hpos : 0 < rho.1.re := rho.2.2.1
    have hre := congrArg Complex.re hn
    rw [hre] at hpos
    have hnonpos : (-2 * ((n : ℂ) + 1)).re ≤ 0 := by
      simp
      positivity
    exact (not_lt_of_ge hnonpos) hpos
  left_inv rho := by
    apply Subtype.ext
    rfl
  right_inv rho := by
    apply Subtype.ext
    rfl

@[simp] theorem aegisLiNontrivialZeroEquivV10_val
    (rho : RiemannNontrivialZeroIndexV2) :
    (aegisLiNontrivialZeroEquivV10 rho).val = rho.1 := rfl

@[simp] theorem aegisLiNontrivialZeroEquivV10_symm_val
    (rho : LiCriterion.NontrivialZero) :
    (aegisLiNontrivialZeroEquivV10.symm rho).1 = rho.val := rfl

/-- Public version of the existing pointwise xi/zeta multiplicity
identification. -/
theorem xi_zeta_multiplicity_eq_v10
    (rho : RiemannNontrivialZeroIndexV2) :
    analyticOrderNatAt LiCriterion.riemannXi rho.1 =
      analyticOrderNatAt riemannZeta rho.1 := by
  simpa using
    li_xi_zeta_multiplicity_eq_v1
      (aegisLiNontrivialZeroEquivV10 rho)

/-- Analytic order of xi is invariant under the provider involution
`rho ↦ 1-rho`. -/
theorem xi_pairedZero_multiplicity_eq_v10
    (rho : LiCriterion.NontrivialZero) :
    analyticOrderNatAt LiCriterion.riemannXi
        (LiCriterion.pairedZero rho).val =
      analyticOrderNatAt LiCriterion.riemannXi rho.val := by
  let g : ℂ → ℂ := fun z => 1 - z
  have hg : AnalyticAt ℂ g rho.val := by
    fun_prop
  have hgd : deriv g rho.val ≠ 0 := by
    dsimp [g]
    simp
  have hcomp :=
    analyticOrderAt_comp_of_deriv_ne_zero
      (f := LiCriterion.riemannXi)
      (g := g)
      (z₀ := rho.val)
      hg hgd
  have hfun :
      LiCriterion.riemannXi ∘ g = LiCriterion.riemannXi := by
    funext z
    dsimp [Function.comp_def, g]
    exact (LiCriterion.xi_functional_equation z).symm
  have horder :
      analyticOrderAt LiCriterion.riemannXi
          (LiCriterion.pairedZero rho).val =
        analyticOrderAt LiCriterion.riemannXi rho.val := by
    rw [LiCriterion.pairedZero_val]
    change
      analyticOrderAt LiCriterion.riemannXi (g rho.val) =
        analyticOrderAt LiCriterion.riemannXi rho.val
    rw [← hcomp]
    rw [hfun]
  exact congrArg ENat.toNat horder

/-- The provider involution is the value-level reflection `rho ↦ 1-rho`
and preserves the multiplicity-weighted Mellin coefficient. -/
theorem pairedZero_weighted_mellin_v10
    (f : ℝ → ℂ) (rho : LiCriterion.NontrivialZero) :
    (analyticOrderNatAt LiCriterion.riemannXi
        (LiCriterion.pairedZero rho).val : ℂ) *
        mellin f (LiCriterion.pairedZero rho).val =
      (analyticOrderNatAt LiCriterion.riemannXi rho.val : ℂ) *
        mellin f (1 - rho.val) := by
  rw [xi_pairedZero_multiplicity_eq_v10, LiCriterion.pairedZero_val]

end AEGIS.WeilZeroCarrierBridgeV10

#print axioms AEGIS.WeilZeroCarrierBridgeV10.xi_zeta_multiplicity_eq_v10
#print axioms AEGIS.WeilZeroCarrierBridgeV10.xi_pairedZero_multiplicity_eq_v10
