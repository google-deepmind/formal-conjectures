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

import WeilXiLogDerivDecompositionV10
import WeilFixedLineArithmeticV10
import WeilFixedLineCompletedGammaV10
import WeilFixedLineZeroSideV10
import Mathlib.Tactic

/-!
AEGIS Ω — whole normalized Weil explicit formula V10.

This module composes the already-isolated fixed-line pieces:

* canonical zero side:
    I_c[2 xi'/xi * H] = 2 Z(f);
* elementary xi poles:
    I_c[(1/s + 1/(s-1)) H] = M f(0) + M f(1);
* completed Gamma factor:
    I_c[(-log(pi)/2 + psi(s/2)/2) H]
      = -ArchConst*f(1) - ArchIntegral(f);
* zeta logarithmic derivative:
    I_c[(zeta'/zeta) H] = -PrimeSum(f).

Together with the pinned-compatible pointwise decomposition of xi'/xi, this
gives the repository-native identity

  Z(f) = M f(0) + M f(1) - WeilExplicitRightSideV1(f).

No sign inequality and no RH conclusion is used or asserted here.

AUTHORITY_EFFECT = NONE.
-/

open Set Filter Topology Complex MeasureTheory
open scoped BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilExplicitFormulaV10

open AEGIS.WeilXiLogDerivDecompositionV10
open AEGIS.WeilFixedLineArithmeticV10
open AEGIS.WeilFixedLineCompletedGammaV10
open AEGIS.WeilFixedLineZeroSideV10

private def PoleProfileV10
    (f : WeilCompactSmoothGV1) (c t : ℝ) : ℂ :=
  (1 / ((c : ℂ) + (t : ℂ) * I) +
    1 / (((c : ℂ) + (t : ℂ) * I) - 1)) *
    WeilPairedMellinProfileV5 f c t

private def GammaProfileV10
    (f : WeilCompactSmoothGV1) (c t : ℝ) : ℂ :=
  WeilCompletedGammaFactorV10 c t *
    WeilPairedMellinProfileV5 f c t

private def ZetaProfileV10
    (f : WeilCompactSmoothGV1) (c t : ℝ) : ℂ :=
  (deriv riemannZeta ((c : ℂ) + (t : ℂ) * I) /
    riemannZeta ((c : ℂ) + (t : ℂ) * I)) *
    WeilPairedMellinProfileV5 f c t

private def XiProfileV10
    (f : WeilCompactSmoothGV1) (c t : ℝ) : ℂ :=
  (2 * _root_.logDeriv LiCriterion.riemannXi
    ((c : ℂ) + (t : ℂ) * I)) *
    WeilPairedMellinProfileV5 f c t

private theorem pole_profile_integrable_v10
    (f : WeilCompactSmoothGV1) (c : ℝ) (hc : 1 < c) :
    Integrable (PoleProfileV10 f c) := by
  have h0 :=
    paired_profile_cauchy_integrable_v10 f c 0 (by
      simp
      linarith)
  have h1 :=
    paired_profile_cauchy_integrable_v10 f c 1 (by
      simpa using hc)
  exact (h0.add h1).congr
    (Filter.Eventually.of_forall fun t => by
      unfold PoleProfileV10
      simp only [sub_zero, Pi.add_apply]
      ring_nf)

private theorem gamma_profile_integrable_v10
    (f : WeilCompactSmoothGV1) (c : ℝ) (hc : 1 < c) :
    Integrable (GammaProfileV10 f c) := by
  exact weil_fixed_line_completed_gamma_integrable_v10 f c hc

private theorem zeta_profile_integrable_v10
    (f : WeilCompactSmoothGV1) (c : ℝ) (hc : 1 < c) :
    Integrable (ZetaProfileV10 f c) := by
  have hn :=
    fixed_line_neg_zeta_logDeriv_integrable_v10 f c hc
  exact hn.neg.congr
    (Filter.Eventually.of_forall fun t => by
      unfold ZetaProfileV10
      simp only [Pi.neg_apply]
      ring_nf)

/-- Pointwise decomposition of the doubled xi profile into the three
normalized explicit-formula pieces. -/
private theorem xi_profile_pointwise_v10
    (f : WeilCompactSmoothGV1) (c t : ℝ) (hc : 1 < c) :
    XiProfileV10 f c t =
      2 * (PoleProfileV10 f c t +
        GammaProfileV10 f c t +
        ZetaProfileV10 f c t) := by
  have hxi :=
    xi_logDeriv_fixed_line_decomposition_v10 c t hc
  unfold XiProfileV10 PoleProfileV10 GammaProfileV10 ZetaProfileV10
  rw [hxi]
  ring

/-- Fixed-line assembly before cancelling the common factor 2. -/
theorem whole_explicit_formula_on_fixed_line_v10
    (f : WeilCompactSmoothGV1) (c : ℝ) (hc : 1 < c) :
    2 * (∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1 f.1 rho) =
      2 * (mellin f.1 0 + mellin f.1 1 -
        WeilExplicitRightSideV1 f.1) := by
  let k : ℂ := 1 / (2 * Real.pi)

  have hP := pole_profile_integrable_v10 f c hc
  have hG := gamma_profile_integrable_v10 f c hc
  have hZ := zeta_profile_integrable_v10 f c hc

  have hsum : Integrable
      (fun t : ℝ =>
        PoleProfileV10 f c t +
          GammaProfileV10 f c t +
          ZetaProfileV10 f c t) :=
    (hP.add hG).add hZ

  have hdecomp :
      (∫ t : ℝ, XiProfileV10 f c t) =
        2 * (∫ t : ℝ,
          (PoleProfileV10 f c t +
            GammaProfileV10 f c t +
            ZetaProfileV10 f c t)) := by
    calc
      (∫ t : ℝ, XiProfileV10 f c t)
        =
      ∫ t : ℝ,
        2 * (PoleProfileV10 f c t +
          GammaProfileV10 f c t +
          ZetaProfileV10 f c t) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall
              (fun t => xi_profile_pointwise_v10 f c t hc)
      _ =
      2 * (∫ t : ℝ,
        (PoleProfileV10 f c t +
          GammaProfileV10 f c t +
          ZetaProfileV10 f c t)) := by
            rw [integral_const_mul]

  have hsplit :
      (∫ t : ℝ,
        (PoleProfileV10 f c t +
          GammaProfileV10 f c t +
          ZetaProfileV10 f c t)) =
      (∫ t : ℝ, PoleProfileV10 f c t) +
      (∫ t : ℝ, GammaProfileV10 f c t) +
      (∫ t : ℝ, ZetaProfileV10 f c t) := by
    have h1 := integral_add (hP.add hG) hZ
    have h2 := integral_add hP hG
    simp only [Pi.add_apply] at h1
    rw [h1, h2]

  have hzero :=
    normalized_two_xi_logDeriv_eq_two_aegis_zero_tsum_v10
      f c hc
  have hpole :=
    fixed_line_poles_eq_mellin_endpoints_v10 f c hc
  have hgamma :=
    weil_fixed_line_completed_gamma_eq_archimedean_v10 f c hc
  have hzeta :=
    fixed_line_zeta_logDeriv_eq_neg_primeSum_v10 f c hc

  have hnorm :
      k * (∫ t : ℝ, XiProfileV10 f c t) =
        2 * (
          k * (∫ t : ℝ, PoleProfileV10 f c t) +
          k * (∫ t : ℝ, GammaProfileV10 f c t) +
          k * (∫ t : ℝ, ZetaProfileV10 f c t)) := by
    rw [hdecomp, hsplit]
    ring

  have hk : k = (1 / (2 * Real.pi) : ℂ) := rfl
  rw [hk] at hnorm

  have hzero' :
      (1 / (2 * Real.pi) : ℂ) *
        (∫ t : ℝ, XiProfileV10 f c t) =
      2 * (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 f.1 rho) := by
    simpa [XiProfileV10] using hzero

  have hpole' :
      (1 / (2 * Real.pi) : ℂ) *
        (∫ t : ℝ, PoleProfileV10 f c t) =
      mellin f.1 0 + mellin f.1 1 := by
    simpa [PoleProfileV10] using hpole

  have hgamma' :
      (1 / (2 * Real.pi) : ℂ) *
        (∫ t : ℝ, GammaProfileV10 f c t) =
      -WeilArchimedeanConstantV1 * f.1 1 -
        WeilArchimedeanIntegralV1 f.1 := by
    simpa [GammaProfileV10] using hgamma

  have hzeta' :
      (1 / (2 * Real.pi) : ℂ) *
        (∫ t : ℝ, ZetaProfileV10 f c t) =
      -WeilPrimeSumV1 f.1 := by
    simpa [ZetaProfileV10] using hzeta

  rw [hzero', hpole', hgamma', hzeta'] at hnorm
  unfold WeilExplicitRightSideV1
  linear_combination hnorm

/-- The first whole repository-native normalized explicit formula.

This is the theorem name used by the RH assumption census as the next whole
identity target.  The fixed line is specialized to c=2; the preceding theorem
shows the result is independent of that arbitrary choice. -/
theorem weil_compact_smooth_explicit_formula_v1
    (f : WeilCompactSmoothGV1) :
    (∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1 f.1 rho) =
      mellin f.1 0 + mellin f.1 1 -
        WeilExplicitRightSideV1 f.1 := by
  have h :=
    whole_explicit_formula_on_fixed_line_v10
      f 2 (by norm_num : (1 : ℝ) < 2)
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  apply (mul_left_cancel₀ htwo)
  simpa only [mul_sub] using h

end AEGIS.WeilExplicitFormulaV10

#print axioms AEGIS.WeilExplicitFormulaV10.whole_explicit_formula_on_fixed_line_v10
#print axioms AEGIS.WeilExplicitFormulaV10.weil_compact_smooth_explicit_formula_v1
