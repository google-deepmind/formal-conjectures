import RHHalfCapV13
import RHMomentGainV13
import Mathlib.Tactic

/-!
AEGIS Ω — the moment gain sharpened by the Cauchy–Schwarz half-cap, V13.

Same route as `RHMomentGainV13.arch_moment_budget` (moment identity, kernel split at
`r` and `2r`), but on `(r, 2r]` the lower bound `h(u) ≥ −e^{u/2}E` is replaced by the
half-cap `h(u) ≥ −e^{u/2}E/2` (`RHHalfCapV13.half_cap_exp_re_lower`).  Result:

  Re Arch(A) ≤ E·( ½·cothTail(2r) − (3/2)·cothTail r + (r/2)e^{r/2}
                   + 2·lamR r·(sinh r − 3 sinh(r/2)) ),

and, below `log 2`, `Re RHS(A) ≤ halfGain r · E`.  Not RH.  AUTHORITY_EFFECT = NONE.
-/

open Set Complex MeasureTheory
open scoped BigOperators ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHHalfCapGainV13
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilWidthArchBudgetV26
open AEGIS.WeilWidthArchIntegralV27
open AEGIS.WeilDiagonalKernelReductionV21
open AEGIS.WeilAutocorrelationExplicitFormulaV10
open AEGIS.RHDyadicDiagonalV13
open AEGIS.RHMomentPiecesV13
open AEGIS.RHMomentGainV13
open AEGIS.RHHalfCapV13

/-- The half-cap gain at log-half-width `r`. -/
def halfGain (r : ℝ) : ℝ :=
  diagonalKappaV21 + cothTail (2 * r) / 2 - (3 / 2) * cothTail r + (r / 2) * Real.exp (r / 2)
    + 2 * lamR r * (Real.sinh r - 3 * Real.sinh (r / 2))

/-- Pointwise majorant on `(r, ∞)` under the half-cap. -/
theorem middle_majorant_half (g : WeilCompactSmoothGV1) (r a u : ℝ) (hr0 : 0 < r)
    (hw : HalfWidthAt g r a) (hru : r < u) :
    budgetIntegrand g r u ≤
      lamR r * energy g.1 * Real.cosh (u / 2) - (3 / 2) * energy g.1 * (1 / Real.sinh u) := by
  have hE := energy_nonnegative g.1
  have hu0 : 0 < u := lt_trans hr0 hru
  have hsu : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu0
  have hk := kernel_nonpos r u hr0 hru.le
  have hh := half_cap_exp_re_lower g r a u hw hru
  have h1 := mul_le_mul_of_nonpos_right hh hk
  have h4 := exp_half_mul u
  have hge : 0 ≤ energy g.1 * ((Real.exp (u / 2) - 1) / Real.sinh u) := by
    apply mul_nonneg hE (div_nonneg _ hsu.le)
    linarith [Real.one_le_exp (by linarith : (0 : ℝ) ≤ u / 2)]
  have h2 : -(Real.exp (u / 2) * (energy g.1 / 2)) *
        (1 / Real.sinh u - lamR r * (1 + Real.exp (-u))) - energy g.1 * (1 / Real.sinh u) =
      (lamR r / 2) * energy g.1 * (Real.exp (u / 2) * (1 + Real.exp (-u))) -
        (3 / 2) * energy g.1 * (1 / Real.sinh u) -
        (1 / 2) * (energy g.1 * ((Real.exp (u / 2) - 1) / Real.sinh u)) := by
    field_simp
    ring
  rw [h4] at h2
  rw [budget_split_form]
  nlinarith

theorem middle_integral_le_half (g : WeilCompactSmoothGV1) (r a : ℝ) (hr0 : 0 < r)
    (hw : HalfWidthAt g r a) :
    (∫ u in Ioc r (2 * r), budgetIntegrand g r u) ≤
      2 * lamR r * energy g.1 * (Real.sinh r - Real.sinh (r / 2)) -
        (3 / 2) * energy g.1 * (cothTail r - cothTail (2 * r)) := by
  have hI : IntegrableOn (budgetIntegrand g r) (Ioc r (2 * r)) :=
    (budgetIntegrand_integrableOn g r).mono_set (fun u hu => lt_trans hr0 hu.1)
  have hA := (cosh_half_integrableOn r (2 * r)).const_mul (lamR r * energy g.1)
  have hB := (integrableOn_inv_sinh_Ioc r (2 * r) hr0).const_mul ((3 / 2) * energy g.1)
  calc
    _ ≤ ∫ u in Ioc r (2 * r), (lamR r * energy g.1 * Real.cosh (u / 2) -
          (3 / 2) * energy g.1 * (1 / Real.sinh u)) := by
      apply setIntegral_mono_on hI (hA.sub hB) measurableSet_Ioc
      intro u hu
      exact middle_majorant_half g r a u hr0 hw hu.1
    _ = _ := by
      rw [integral_sub hA hB, integral_const_mul, integral_const_mul,
        integral_cosh_half r (2 * r) (by linarith),
        integral_inv_sinh_Ioc r (2 * r) hr0 (by linarith)]
      have h2 : 2 * r / 2 = r := by ring
      rw [h2]
      ring

/-- **Archimedean budget with moment gain and half-cap.** -/
theorem arch_half_cap_budget (g : WeilCompactSmoothGV1) (r a : ℝ) (hr0 : 0 < r)
    (hw : HalfWidthAt g r a) (hm : WeilMomentConditionsV1 g) :
    (WeilArchimedeanIntegralV1 (WeilAutocorrelationV1 g)).re ≤
      energy g.1 * (cothTail (2 * r) / 2 - (3 / 2) * cothTail r + (r / 2) * Real.exp (r / 2)
        + 2 * lamR r * (Real.sinh r - 3 * Real.sinh (r / 2))) := by
  have hF := budgetIntegrand_integrableOn g r
  have hsplit1 : (∫ u in Ioi (0 : ℝ), budgetIntegrand g r u) =
      (∫ u in Ioc (0 : ℝ) r, budgetIntegrand g r u) + ∫ u in Ioi r, budgetIntegrand g r u := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hr0.le,
      setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hF.mono_set (fun u hu => hu.1))
        (hF.mono_set (fun u hu => lt_trans hr0 hu))]
  have hsplit2 : (∫ u in Ioi r, budgetIntegrand g r u) =
      (∫ u in Ioc r (2 * r), budgetIntegrand g r u) +
        ∫ u in Ioi (2 * r), budgetIntegrand g r u := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi (by linarith : r ≤ 2 * r),
      setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hF.mono_set (fun u hu => lt_trans hr0 hu.1))
        (hF.mono_set (fun u hu => by
          change 2 * r < u at hu; change (0 : ℝ) < u; linarith))]
  rw [arch_eq_budget_integral g r hm, hsplit1, hsplit2, tail_integral_eq g r a hr0 hw]
  have hi := inner_integral_le g r hr0
  have hmid := middle_integral_le_half g r a hr0 hw
  nlinarith

/-- **Half-cap diagonal.**  Below `log 2`, `Re RHS(A) ≤ halfGain r · E`. -/
theorem half_cap_diagonal (g : WeilCompactSmoothGV1) (r a : ℝ) (hr0 : 0 < r)
    (hlog : 2 * r < Real.log 2) (hw : HalfWidthAt g r a) (hm : WeilMomentConditionsV1 g) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ halfGain r * energy g.1 := by
  have hp := prime_sum_zero_of_halfWidth g r a hw hlog
  have hb := arch_half_cap_budget g r a hr0 hw hm
  change (B g g).re ≤ _
  rw [actual_diagonal_rhs_decomposition g hp]
  have heq : halfGain r * energy g.1 = diagonalKappaV21 * energy g.1 +
      energy g.1 * (cothTail (2 * r) / 2 - (3 / 2) * cothTail r + (r / 2) * Real.exp (r / 2)
        + 2 * lamR r * (Real.sinh r - 3 * Real.sinh (r / 2))) := by
    unfold halfGain; ring
  rw [heq]
  linarith

end AEGIS.RHHalfCapGainV13

#print axioms AEGIS.RHHalfCapGainV13.middle_majorant_half
#print axioms AEGIS.RHHalfCapGainV13.arch_half_cap_budget
#print axioms AEGIS.RHHalfCapGainV13.half_cap_diagonal
