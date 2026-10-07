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

import AEGISOverlay.RHKreinFiniteCertificateDataV1
import RHKreinRationalCertificateV1
import Mathlib.Tactic

/-!
# Assembly boundary for the finite Krein certificate

The infinite tail is already unconditional in
`RHKreinRationalCertificateV1.corrected_symbol_tail_nonnegative`.
This file isolates the only remaining analytic obligation to the positive
finite interval `[0,300]`.

It also proves the evenness needed to reflect that finite interval to
`[-300,0]`; no numerical certificate is used for these symmetry facts.

The serialized 2199-cell payload is imported, but its stored lower bounds
are not promoted to analytic inequalities here.  That is the remaining
kernel-checker obligation.

AUTHORITY_EFFECT = NONE.
RH is not asserted here.
-/

open Complex
open scoped BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinFiniteCertificateAssemblyV1

open AEGIS.RHKreinFiniteCertificateDataV1
open AEGIS.RHKreinDigammaMonotonicityV1
open AEGIS.RHKreinPrimeSymbolV1
open AEGIS.RHKreinSymbolIntegrationV1
open AEGIS.RHKreinExplicitCorrectionV1
open AEGIS.RHKreinRationalCertificateV1

/-- The exact pointwise expression consumed by `PointwiseCertificate`. -/
def correctedExpression (t : ℝ) : ℝ :=
  (t ^ 2 + 1 / 4) ^ 2 * (symbol t - 1 / 16) + correctionSymbol t

/-- The normalized excess used by the numerical 2199-cell certificate. -/
def normalizedExcess (t : ℝ) : ℝ :=
  symbol t + correctionSymbol t / (t ^ 2 + 1 / 4) ^ 2 - 1 / 16

/-- The polynomial weight is strictly positive at every real frequency. -/
theorem weight_pos_v1 (t : ℝ) :
    0 < (t ^ 2 + 1 / 4) ^ 2 := by
  have hbase : 0 < t ^ 2 + 1 / 4 := by
    nlinarith [sq_nonneg t]
  positivity

/-- The checker-normalized expression and the pointwise certificate are
exactly related by the positive polynomial weight. -/
theorem correctedExpression_eq_weight_mul_normalizedExcess_v1 (t : ℝ) :
    correctedExpression t =
      (t ^ 2 + 1 / 4) ^ 2 * normalizedExcess t := by
  unfold correctedExpression normalizedExcess
  have hw : (t ^ 2 + 1 / 4) ^ 2 ≠ 0 := (weight_pos_v1 t).ne'
  field_simp [hw]
  ring

/-- A positive normalized lower bound is sufficient for the actual pointwise
certificate at that frequency. -/
theorem correctedExpression_nonnegative_of_normalizedExcess_v1
    (t : ℝ) (h : 0 ≤ normalizedExcess t) :
    0 ≤ correctedExpression t := by
  rw [correctedExpression_eq_weight_mul_normalizedExcess_v1]
  exact mul_nonneg (weight_pos_v1 t).le h

/-- The real part of the quarter-line digamma is an even function of the
angular frequency.  This follows from the already-proved dependence on t^2. -/
theorem digamma_quarter_even_v1 (t : ℝ) :
    (Complex.digamma ((1 / 4 : ℂ) + ((-t : ℝ) : ℂ) * I / 2)).re =
      (Complex.digamma ((1 / 4 : ℂ) + (t : ℂ) * I / 2)).re := by
  apply le_antisymm
  · exact digamma_quarter_mono_of_sq_le (-t) t (by simp)
  · exact digamma_quarter_mono_of_sq_le t (-t) (by simp)

/-- The full first-post-log2 Weil symbol is even. -/
theorem symbol_even_v1 (t : ℝ) :
    symbol (-t) = symbol t := by
  unfold symbol archSymbol
  rw [digamma_quarter_even_v1]
  have hc :
      Real.cos ((-t) * Real.log 2) =
        Real.cos (t * Real.log 2) := by
    rw [show (-t) * Real.log 2 = -(t * Real.log 2) by ring, Real.cos_neg]
  rw [hc]

/-- Every hat contribution in the explicit correction is even. -/
private theorem hat_sum_even_v1 (t : ℝ) :
    (∑ j : Fin 199,
      (hatCoefficient j : ℝ) * Real.cos ((-t) * hatCenter j)) =
    ∑ j : Fin 199,
      (hatCoefficient j : ℝ) * Real.cos (t * hatCenter j) := by
  apply Finset.sum_congr rfl
  intro j _hj
  rw [show (-t) * hatCenter j = -(t * hatCenter j) by ring, Real.cos_neg]

/-- The five derivative columns have the parity encoded by the certificate:
odd powers are paired with sine and even powers with cosine, so the whole
spline correction is even. -/
private theorem spline_sum_even_v1 (t : ℝ) :
    (∑ j : Fin 5, (splineCoefficient j : ℝ) * (-t) ^ j.val *
      (if j.val % 2 = 0 then Real.cos ((-t) * (1619 / 2000))
       else Real.sin ((-t) * (1619 / 2000)))) =
    ∑ j : Fin 5, (splineCoefficient j : ℝ) * t ^ j.val *
      (if j.val % 2 = 0 then Real.cos (t * (1619 / 2000))
       else Real.sin (t * (1619 / 2000))) := by
  apply Finset.sum_congr rfl
  intro j _hj
  fin_cases j
  all_goals norm_num
  all_goals ring

/-- The exact genuine-function correction symbol is even. -/
theorem correctionSymbol_even_v1 (t : ℝ) :
    correctionSymbol (-t) = correctionSymbol t := by
  unfold correctionSymbol
  have h100 : (-t) / 100 = -(t / 100) := by ring
  have h2000 : (-t) / 2000 = -(t / 2000) := by ring
  rw [h100, Real.sinc_neg, h2000, Real.sinc_neg,
    hat_sum_even_v1, spline_sum_even_v1]

/-- Hence the complete corrected expression is orientation-free. -/
theorem correctedExpression_even_v1 (t : ℝ) :
    correctedExpression (-t) = correctedExpression t := by
  unfold correctedExpression
  rw [symbol_even_v1, correctionSymbol_even_v1]
  ring

/-- Analytic meaning of one serialized cell.  The stored dyadic rational
must be a genuine lower bound for the normalized excess throughout that
cell.  This is exactly the assertion the finite checker must kernel-justify. -/
def CellAnalyticSoundV1 (c : FiniteCellV1) : Prop :=
  ∀ t : ℝ, (c.lo : ℝ) ≤ t → t ≤ (c.hi : ℝ) →
    (lowerValue c : ℝ) ≤ normalizedExcess t

/-- All 2199 serialized cells have their intended analytic meaning. -/
def AllCellsAnalyticSoundV1 : Prop :=
  ∀ c, c ∈ finiteCells → CellAnalyticSoundV1 c

/-- The only remaining analytic theorem needed after the already-closed tail. -/
def FiniteIntervalCertificateV1 : Prop :=
  ∀ t : ℝ, 0 ≤ t → t ≤ 300 → 0 ≤ correctedExpression t


/-- Exact reduction of the positive finite interval to the 2199 cell
soundness obligations.  Coverage and positivity of every stored dyadic lower
endpoint come from the kernel-checked payload theorem, not from floating
point output. -/
theorem finiteIntervalCertificate_of_allCellsAnalyticSound_v1
    (hcells : AllCellsAnalyticSoundV1) :
    FiniteIntervalCertificateV1 := by
  intro t ht0 ht300
  obtain ⟨c, hc, hlo, hhi, hlower⟩ :=
    finiteCells_cover_zero_three_hundred_v1 ht0 ht300
  have hsound := hcells c hc t hlo hhi
  have hlower0q : (0 : ℚ) < lowerValue c := by
    exact (by norm_num : (0 : ℚ) < 1 / 100000).trans hlower
  have hlower0 : (0 : ℝ) < (lowerValue c : ℝ) := by
    exact_mod_cast hlower0q
  apply correctedExpression_nonnegative_of_normalizedExcess_v1
  exact hlower0.le.trans hsound

/-- Once the positive finite interval is kernel-certified, evenness plus the
existing tail theorem gives the full pointwise certificate consumed by the
actual Weil quadratic margin theorem. -/
theorem pointwiseCertificate_of_finite_interval_v1
    (hfinite : FiniteIntervalCertificateV1) :
    PointwiseCertificate := by
  intro t
  change 0 ≤ correctedExpression t
  by_cases htail : 300 ≤ |t|
  · unfold correctedExpression
    exact corrected_symbol_tail_nonnegative t htail
  · have habs300 : |t| ≤ 300 := (lt_of_not_ge htail).le
    have hfiniteAbs := hfinite |t| (abs_nonneg t) habs300
    have heven : correctedExpression |t| = correctedExpression t := by
      by_cases ht : 0 ≤ t
      · rw [abs_of_nonneg ht]
      · have htn : t ≤ 0 := le_of_not_ge ht
        rw [abs_of_nonpos htn, correctedExpression_even_v1]
    rw [← heven]
    exact hfiniteAbs

/-- Therefore the entire pointwise order-19 Krein certificate reduces to
one exact statement: analytic soundness of the 2199 serialized cells. -/
theorem pointwiseCertificate_of_allCellsAnalyticSound_v1
    (hcells : AllCellsAnalyticSoundV1) :
    PointwiseCertificate :=
  pointwiseCertificate_of_finite_interval_v1
    (finiteIntervalCertificate_of_allCellsAnalyticSound_v1 hcells)

/-- Once the 2199 analytic cell obligations are discharged, the existing
genuine correction theorem yields the actual repository zero-quadratic
margin on every moment-zero packet of logarithmic half-width at most 2/5. -/
theorem actual_zero_quadratic_margin_of_allCellsAnalyticSound_v1
    (hcells : AllCellsAnalyticSoundV1)
    (g : WeilCompactSmoothGV1) (r a : ℝ)
    (hr0 : 0 ≤ r) (hr : r ≤ 2 / 5)
    (hw : AEGIS.RHDyadicDiagonalV13.HalfWidthAt g r a)
    (hm : WeilMomentConditionsV1 g) :
    (1 / 16) * AEGIS.WeilDisjointEnergyV2.energy g.1 ≤
      (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  exact actual_zero_quadratic_margin
    (pointwiseCertificate_of_allCellsAnalyticSound_v1 hcells)
    g r a hr0 hr hw hm

end AEGIS.RHKreinFiniteCertificateAssemblyV1

#print axioms AEGIS.RHKreinFiniteCertificateAssemblyV1.correctedExpression_eq_weight_mul_normalizedExcess_v1
#print axioms AEGIS.RHKreinFiniteCertificateAssemblyV1.digamma_quarter_even_v1
#print axioms AEGIS.RHKreinFiniteCertificateAssemblyV1.symbol_even_v1
#print axioms AEGIS.RHKreinFiniteCertificateAssemblyV1.correctionSymbol_even_v1
#print axioms AEGIS.RHKreinFiniteCertificateAssemblyV1.correctedExpression_even_v1
#print axioms AEGIS.RHKreinFiniteCertificateAssemblyV1.finiteIntervalCertificate_of_allCellsAnalyticSound_v1
#print axioms AEGIS.RHKreinFiniteCertificateAssemblyV1.pointwiseCertificate_of_finite_interval_v1
#print axioms AEGIS.RHKreinFiniteCertificateAssemblyV1.pointwiseCertificate_of_allCellsAnalyticSound_v1
#print axioms AEGIS.RHKreinFiniteCertificateAssemblyV1.actual_zero_quadratic_margin_of_allCellsAnalyticSound_v1
