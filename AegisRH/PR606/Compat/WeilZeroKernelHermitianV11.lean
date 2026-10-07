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

import WeilZeroTwoPointV11
import WeilAutocorrelationExplicitFormulaV10
import WeilAutocorrelationRealityV1
import WeilAutocorrelationPoleAggregationV1
import Mathlib.Tactic

/-!
Fork-local compatibility overlay.

Authoritative AEGIS source anchor:
  Aegis-Omega/AEGIS-OMEGA@589adf0480bd4d7c12c9828027ea6228398377f4

The theorem/definition signatures are unchanged. This fork copy repairs only
Lean 4.33.1 elaboration of the already-derived Hermitian kernel identity.
-/


/-!
AEGIS Ω — Hermitian symmetry of the canonical zero translation kernel V11.

Instead of re-proving multiplicity preservation under complex conjugation at
the zero-carrier level, this module derives the symmetry from two already
repository-native facts:

1. the whole explicit formula identifies the canonical zero quadratic with
   the negative arithmetic RHS on the moment-zero class;
2. the arithmetic RHS of every multiplicative autocorrelation is real.

Apply reality to the two translated packets with coefficients 1 and I.  The
exact V11 two-point expansion then forces

  K_g(-t) = conj(K_g(t)).

This is logically equivalent to the spectral reflection needed by the
restricted Weil criterion, but it reuses the stronger assembled arithmetic
transport rather than adding a new conjugation-multiplicity dependency.

AUTHORITY_EFFECT = NONE.
-/

open Set Filter Topology Complex MeasureTheory
open scoped BigOperators ComplexConjugate

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilZeroKernelHermitianV11

open AEGIS.WeilZeroTranslationV11
open AEGIS.WeilZeroTwoPointV11
open AEGIS.WeilAutocorrelationExplicitFormulaV10

/-- The exact two-point translated packet preserves the repository's two
Mellin moment constraints. -/
theorem twoPointTranslate_preserves_moments_v11
    (g : WeilCompactSmoothGV1) (d : ℝ) (c : ℂ)
    (hm : WeilMomentConditionsV1 g) :
    WeilMomentConditionsV1 (WeilTwoPointTranslateV11 g d c) := by
  have hg0 : mellin g.1 0 = 0 := by
    exact (weil_mellin_zero_eq_moment0_v1 g).trans hm.1
  have hg1 : mellin g.1 1 = 0 := by
    exact (weil_mellin_one_eq_moment1_v1 g).trans hm.2
  constructor
  · rw [← weil_mellin_zero_eq_moment0_v1
      (WeilTwoPointTranslateV11 g d c)]
    rw [mellin_twoPointTranslate_v11]
    simp [hg0]
  · rw [← weil_mellin_one_eq_moment1_v1
      (WeilTwoPointTranslateV11 g d c)]
    rw [mellin_twoPointTranslate_v11]
    simp [hg1]

/-- On the exact moment-zero domain, the canonical zero quadratic is real.
The proof is routed through the whole explicit formula and the independently
proved arithmetic reality theorem. -/
theorem autocorrelation_zero_quadratic_real_v11
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g) :
    (WeilAutocorrelationZeroQuadraticV11 g).im = 0 := by
  have hEF :=
    autocorrelation_explicit_formula_v10 g hm
  have hR :=
    weil_autocorrelation_explicit_right_side_real_v1 g
  rw [hEF] at hR
  change (-WeilAutocorrelationZeroQuadraticV11 g).im = 0 at hR
  simpa using hR

/-- The canonical zero translation kernel satisfies the exact Hermitian
reflection law. -/
theorem zero_translation_kernel_neg_eq_conj_v11
    (g : WeilCompactSmoothGV1) (d : ℝ)
    (hm : WeilMomentConditionsV1 g) :
    WeilZeroTranslationKernelV11 g (-d) =
      conj (WeilZeroTranslationKernelV11 g d) := by
  let Q0 := WeilAutocorrelationZeroQuadraticV11 g
  let Kp := WeilZeroTranslationKernelV11 g d
  let Km := WeilZeroTranslationKernelV11 g (-d)

  have hQ0 : Q0.im = 0 := by
    simpa [Q0] using autocorrelation_zero_quadratic_real_v11 g hm

  have hm1 :=
    twoPointTranslate_preserves_moments_v11 g d 1 hm
  have hmI :=
    twoPointTranslate_preserves_moments_v11 g d I hm

  have hQ1 :
      (WeilAutocorrelationZeroQuadraticV11
        (WeilTwoPointTranslateV11 g d 1)).im = 0 :=
    autocorrelation_zero_quadratic_real_v11
      (WeilTwoPointTranslateV11 g d 1) hm1

  have hQI :
      (WeilAutocorrelationZeroQuadraticV11
        (WeilTwoPointTranslateV11 g d I)).im = 0 :=
    autocorrelation_zero_quadratic_real_v11
      (WeilTwoPointTranslateV11 g d I) hmI

  have h1 :=
    congrArg Complex.im
      (twoPoint_zero_quadratic_expansion_v11 g d 1)
  have hI :=
    congrArg Complex.im
      (twoPoint_zero_quadratic_expansion_v11 g d I)

  change
    (WeilAutocorrelationZeroQuadraticV11
      (WeilTwoPointTranslateV11 g d 1)).im =
      ((1 + (1 : ℂ) * conj (1 : ℂ)) * Q0 +
        (1 : ℂ) * Kp + conj (1 : ℂ) * Km).im at h1
  change
    (WeilAutocorrelationZeroQuadraticV11
      (WeilTwoPointTranslateV11 g d I)).im =
      ((1 + I * conj I) * Q0 +
        I * Kp + conj I * Km).im at hI

  rw [hQ1] at h1
  rw [hQI] at hI

  have him : Kp.im + Km.im = 0 := by
    simp [hQ0] at h1
    linarith

  have hre : Kp.re = Km.re := by
    simp [hQ0, Complex.mul_im, Complex.mul_re] at hI
    linarith

  apply Complex.ext
  · simp only [conj_re]
    exact hre.symm
  · simp only [conj_im]
    linarith

/-- Consequently the V11 two-point expansion has the familiar Hermitian
quadratic form. -/
theorem twoPoint_zero_quadratic_hermitian_v11
    (g : WeilCompactSmoothGV1) (d : ℝ) (c : ℂ)
    (hm : WeilMomentConditionsV1 g) :
    WeilAutocorrelationZeroQuadraticV11
        (WeilTwoPointTranslateV11 g d c) =
      (1 + c * conj c) *
        WeilAutocorrelationZeroQuadraticV11 g +
      c * WeilZeroTranslationKernelV11 g d +
      conj c * conj (WeilZeroTranslationKernelV11 g d) := by
  rw [twoPoint_zero_quadratic_expansion_v11,
    zero_translation_kernel_neg_eq_conj_v11 g d hm]

end AEGIS.WeilZeroKernelHermitianV11

#print axioms AEGIS.WeilZeroKernelHermitianV11.twoPointTranslate_preserves_moments_v11
#print axioms AEGIS.WeilZeroKernelHermitianV11.autocorrelation_zero_quadratic_real_v11
#print axioms AEGIS.WeilZeroKernelHermitianV11.zero_translation_kernel_neg_eq_conj_v11
#print axioms AEGIS.WeilZeroKernelHermitianV11.twoPoint_zero_quadratic_hermitian_v11
