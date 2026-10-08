import RHThreeCellV13
import RHBonusGainV13
import Mathlib.Tactic

/-!
AEGIS Ω — the moment gain with the three-cell cap, V13.

Multiplier `λ = lamR t`, threshold `t`, half-width `r`, `s = 2r/3 < t ≤ r`.  With the
three-cell cap relaxed to `c = 3/4` (`RHThreeCellV13`, `71/100 ≤ 3/4`) and
`c·e^{t/2} ≤ 13/16`, the pieces of the budget integral are bounded by

* `(0, s]`:    kernel `≥ 0`, `h ≤ e^{u/2}E`                               (`inner_majorant`);
* `(s, t]`:    kernel `≥ 0`, `h ≤ (3/4)e^{u/2}E`                           (three-cell);
* `(t, r]`:    kernel `≤ 0`, `h ≥ −(3/4)e^{u/2}E`, plus the `½`-bonus       (three-cell);
* `(r, 2r]`:   kernel `≤ 0`, half-cap plus the `½`-bonus                    (`RHBonusGainV13`);
* `(2r, ∞)`:   `h = 0`.

Result: `Re RHS(A) ≤ cellGain t r · E` below `log 2`.  Not RH.  AUTHORITY_EFFECT = NONE.
-/

open Set Complex MeasureTheory
open scoped BigOperators ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHThreeCellGainV13
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilWidthArchBudgetV26
open AEGIS.WeilWidthArchIntegralV27
open AEGIS.WeilDiagonalKernelReductionV21
open AEGIS.WeilAutocorrelationExplicitFormulaV10
open AEGIS.RHDyadicDiagonalV13
open AEGIS.RHMomentPiecesV13
open AEGIS.RHMomentGainV13
open AEGIS.RHThresholdGainV13
open AEGIS.RHBonusGainV13
open AEGIS.RHThreeCellV13

/-- The Archimedean part of the three-cell gain (`s = 2r/3`). -/
def cellArch (t r : ℝ) : ℝ :=
  (2 * r / 3) / 2 * Real.exp (t / 2) - 4 * lamR t * Real.sinh ((2 * r / 3) / 2)
    + (13 / 16 - 1) * (cothTail (2 * r / 3) - cothTail t)
    - 4 * (3 / 4) * lamR t * (Real.sinh (t / 2) - Real.sinh ((2 * r / 3) / 2))
    - (1 + 3 / 4) * (cothTail t - cothTail r)
    + 4 * (3 / 4) * lamR t * (Real.sinh (r / 2) - Real.sinh (t / 2)) - (3 / 4) * (r - t) / 2
    + 2 * lamR t * (Real.sinh r - Real.sinh (r / 2))
    - (3 / 2) * (cothTail r - cothTail (2 * r)) - r / 4
    - cothTail (2 * r)

/-- The three-cell gain. -/
def cellGain (t r : ℝ) : ℝ := diagonalKappaV21 + cellArch t r

theorem inner_integral_le_s (g : WeilCompactSmoothGV1) (t s : ℝ) (hs0 : 0 < s) (hst : s ≤ t) :
    (∫ u in Ioc (0 : ℝ) s, budgetIntegrand g t u) ≤
      energy g.1 * (s / 2 * Real.exp (t / 2)) - 4 * lamR t * energy g.1 * Real.sinh (s / 2) := by
  have hI : IntegrableOn (budgetIntegrand g t) (Ioc (0 : ℝ) s) :=
    (budgetIntegrand_integrableOn g t).mono_set (fun u hu => hu.1)
  have hA : IntegrableOn (fun u : ℝ => 2 * lamR t * energy g.1 * Real.cosh (u / 2))
      (Ioc (0 : ℝ) s) := (cosh_half_integrableOn 0 s).const_mul (2 * lamR t * energy g.1)
  have hM : IntegrableOn (fun u : ℝ => energy g.1 * (Real.exp (t / 2) / 2) -
      2 * lamR t * energy g.1 * Real.cosh (u / 2)) (Ioc (0 : ℝ) s) :=
    continuous_const.integrableOn_Ioc.sub hA
  calc
    _ ≤ ∫ u in Ioc (0 : ℝ) s, (energy g.1 * (Real.exp (t / 2) / 2) -
          2 * lamR t * energy g.1 * Real.cosh (u / 2)) := by
      apply setIntegral_mono_on hI hM measurableSet_Ioc
      intro u hu
      exact inner_majorant g t u hu.1 (le_trans hu.2 hst)
    _ = _ := by
      rw [integral_sub continuous_const.integrableOn_Ioc hA, setIntegral_const,
        integral_const_mul, integral_cosh_half 0 s hs0.le, smul_eq_mul,
        Real.volume_real_Ioc_of_le hs0.le]
      simp only [zero_div, Real.sinh_zero, sub_zero]
      ring

/-- Upper three-cell majorant on `(s, t]`. -/
theorem cell_upper_majorant (g : WeilCompactSmoothGV1) (t r a u : ℝ) (hw : HalfWidthAt g r a)
    (h3 : 2 * r < 3 * u) (hu0 : 0 < u) (hut : u ≤ t) (hexp : Real.exp (t / 2) ≤ 13 / 12) :
    budgetIntegrand g t u ≤
      energy g.1 * (13 / 16 - 1) * (1 / Real.sinh u)
        - 2 * (3 / 4) * lamR t * energy g.1 * Real.cosh (u / 2) := by
  have hE := energy_nonnegative g.1
  have hsu : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu0
  have hk := kernel_nonneg t u hu0 hut
  have hup := (three_cell_exp_re_bounds g r a u hw h3 hu0).2
  have he2 := Real.exp_pos (u / 2)
  have hup' : Real.exp u * (WeilAutocorrelationV1 g (Real.exp u)).re ≤
      Real.exp (u / 2) * ((3 / 4) * energy g.1) := by
    nlinarith [mul_le_mul_of_nonneg_left (by linarith : (71 / 100 : ℝ) * energy g.1 ≤
      (3 / 4) * energy g.1) he2.le]
  have h1 := mul_le_mul_of_nonneg_right hup' hk
  have h4 := exp_half_mul u
  have heu : Real.exp (u / 2) ≤ 13 / 12 :=
    le_trans (Real.exp_le_exp.mpr (by linarith)) hexp
  have hc : energy g.1 * ((3 / 4) * Real.exp (u / 2) - 1) / Real.sinh u ≤
      energy g.1 * (13 / 16 - 1) / Real.sinh u := by
    apply div_le_div_of_nonneg_right _ hsu.le
    apply mul_le_mul_of_nonneg_left _ hE
    linarith
  have h2 : Real.exp (u / 2) * ((3 / 4) * energy g.1) *
        (1 / Real.sinh u - lamR t * (1 + Real.exp (-u))) - energy g.1 * (1 / Real.sinh u) =
      energy g.1 * ((3 / 4) * Real.exp (u / 2) - 1) / Real.sinh u
        - (3 / 4) * lamR t * energy g.1 * (Real.exp (u / 2) * (1 + Real.exp (-u))) := by
    field_simp
    ring
  rw [h4] at h2
  rw [budget_split_form]
  have hc' : energy g.1 * (13 / 16 - 1) / Real.sinh u =
      energy g.1 * (13 / 16 - 1) * (1 / Real.sinh u) := by ring
  linarith

/-- Lower three-cell majorant with the bonus on `(t, r]`. -/
theorem cell_lower_majorant (g : WeilCompactSmoothGV1) (t r a u : ℝ) (hw : HalfWidthAt g r a)
    (ht0 : 0 < t) (htu : t ≤ u) (h3 : 2 * r < 3 * u) (hu1 : u ≤ 1) :
    budgetIntegrand g t u ≤
      2 * (3 / 4) * lamR t * energy g.1 * Real.cosh (u / 2)
        - (1 + 3 / 4) * energy g.1 * (1 / Real.sinh u) - (3 / 4) * energy g.1 / 2 := by
  have hE := energy_nonnegative g.1
  have hu0 : 0 < u := lt_of_lt_of_le ht0 htu
  have hsu : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu0
  have hk := kernel_nonpos t u ht0 htu
  have hlo := (three_cell_exp_re_bounds g r a u hw h3 hu0).1
  have he2 := Real.exp_pos (u / 2)
  have hlo' : -(Real.exp (u / 2) * ((3 / 4) * energy g.1)) ≤
      Real.exp u * (WeilAutocorrelationV1 g (Real.exp u)).re := by
    nlinarith [mul_le_mul_of_nonneg_left (by linarith : (71 / 100 : ℝ) * energy g.1 ≤
      (3 / 4) * energy g.1) he2.le]
  have h1 := mul_le_mul_of_nonpos_right hlo' hk
  have h4 := exp_half_mul u
  have hge : energy g.1 / 2 ≤ energy g.1 * ((Real.exp (u / 2) - 1) / Real.sinh u) := by
    have := mul_le_mul_of_nonneg_left (half_le_bonus u hu0 hu1) hE
    linarith
  have h2 : -(Real.exp (u / 2) * ((3 / 4) * energy g.1)) *
        (1 / Real.sinh u - lamR t * (1 + Real.exp (-u))) - energy g.1 * (1 / Real.sinh u) =
      (3 / 4) * lamR t * energy g.1 * (Real.exp (u / 2) * (1 + Real.exp (-u))) -
        (1 + 3 / 4) * energy g.1 * (1 / Real.sinh u) -
        (3 / 4) * (energy g.1 * ((Real.exp (u / 2) - 1) / Real.sinh u)) := by
    field_simp
    ring
  rw [h4] at h2
  rw [budget_split_form]
  nlinarith

theorem upper_integral_le (g : WeilCompactSmoothGV1) (t r a : ℝ) (hw : HalfWidthAt g r a)
    (hs0 : 0 < 2 * r / 3) (hst : 2 * r / 3 ≤ t) (hexp : Real.exp (t / 2) ≤ 13 / 12) :
    (∫ u in Ioc (2 * r / 3) t, budgetIntegrand g t u) ≤
      energy g.1 * (13 / 16 - 1) * (cothTail (2 * r / 3) - cothTail t)
        - 4 * (3 / 4) * lamR t * energy g.1 *
          (Real.sinh (t / 2) - Real.sinh ((2 * r / 3) / 2)) := by
  have hI : IntegrableOn (budgetIntegrand g t) (Ioc (2 * r / 3) t) :=
    (budgetIntegrand_integrableOn g t).mono_set (fun u hu => lt_trans hs0 hu.1)
  have hB : IntegrableOn (fun u : ℝ => energy g.1 * (13 / 16 - 1) * (1 / Real.sinh u))
      (Ioc (2 * r / 3) t) :=
    (integrableOn_inv_sinh_Ioc (2 * r / 3) t hs0).const_mul _
  have hA : IntegrableOn (fun u : ℝ => 2 * (3 / 4) * lamR t * energy g.1 * Real.cosh (u / 2))
      (Ioc (2 * r / 3) t) := (cosh_half_integrableOn (2 * r / 3) t).const_mul _
  calc
    _ ≤ ∫ u in Ioc (2 * r / 3) t, (energy g.1 * (13 / 16 - 1) * (1 / Real.sinh u)
          - 2 * (3 / 4) * lamR t * energy g.1 * Real.cosh (u / 2)) := by
      apply setIntegral_mono_on hI (hB.sub hA) measurableSet_Ioc
      intro u hu
      exact cell_upper_majorant g t r a u hw (by linarith [hu.1]) (lt_trans hs0 hu.1) hu.2 hexp
    _ = _ := by
      rw [integral_sub hB hA, integral_const_mul, integral_const_mul,
        integral_inv_sinh_Ioc (2 * r / 3) t hs0 hst, integral_cosh_half (2 * r / 3) t hst]
      ring

theorem lower_integral_le (g : WeilCompactSmoothGV1) (t r a : ℝ) (hw : HalfWidthAt g r a)
    (ht0 : 0 < t) (htr : t ≤ r) (hst : 2 * r / 3 < t) (hr1 : r ≤ 1) :
    (∫ u in Ioc t r, budgetIntegrand g t u) ≤
      4 * (3 / 4) * lamR t * energy g.1 * (Real.sinh (r / 2) - Real.sinh (t / 2))
        - (1 + 3 / 4) * energy g.1 * (cothTail t - cothTail r)
        - (3 / 4) * energy g.1 / 2 * (r - t) := by
  have hI : IntegrableOn (budgetIntegrand g t) (Ioc t r) :=
    (budgetIntegrand_integrableOn g t).mono_set (fun u hu => lt_trans ht0 hu.1)
  have hA := (cosh_half_integrableOn t r).const_mul (2 * (3 / 4) * lamR t * energy g.1)
  have hB := (integrableOn_inv_sinh_Ioc t r ht0).const_mul ((1 + 3 / 4) * energy g.1)
  have hC : IntegrableOn (fun _ : ℝ => (3 / 4) * energy g.1 / 2) (Ioc t r) :=
    continuous_const.integrableOn_Ioc
  have hAB : IntegrableOn (fun u : ℝ => 2 * (3 / 4) * lamR t * energy g.1 * Real.cosh (u / 2)
      - (1 + 3 / 4) * energy g.1 * (1 / Real.sinh u)) (Ioc t r) := hA.sub hB
  calc
    _ ≤ ∫ u in Ioc t r, (2 * (3 / 4) * lamR t * energy g.1 * Real.cosh (u / 2)
          - (1 + 3 / 4) * energy g.1 * (1 / Real.sinh u) - (3 / 4) * energy g.1 / 2) := by
      apply setIntegral_mono_on hI (hAB.sub hC) measurableSet_Ioc
      intro u hu
      exact cell_lower_majorant g t r a u hw ht0 hu.1.le (by linarith [hu.1])
        (le_trans hu.2 hr1)
    _ = _ := by
      rw [integral_sub hAB hC, integral_sub hA hB, integral_const_mul, integral_const_mul,
        integral_cosh_half t r htr, integral_inv_sinh_Ioc t r ht0 htr, setIntegral_const,
        smul_eq_mul, Real.volume_real_Ioc_of_le htr]
      ring

/-- **Archimedean budget with the three-cell cap.** -/
theorem arch_cell_budget (g : WeilCompactSmoothGV1) (t r a : ℝ) (hr0 : 0 < r)
    (hst : 2 * r / 3 < t) (htr : t ≤ r) (hr1 : 2 * r ≤ 1)
    (hexp : Real.exp (t / 2) ≤ 13 / 12) (hw : HalfWidthAt g r a)
    (hm : WeilMomentConditionsV1 g) :
    (WeilArchimedeanIntegralV1 (WeilAutocorrelationV1 g)).re ≤ energy g.1 * cellArch t r := by
  have hs0 : 0 < 2 * r / 3 := by linarith
  have ht0 : 0 < t := lt_trans hs0 hst
  have hF := budgetIntegrand_integrableOn g t
  have hs1 : (∫ u in Ioi (0 : ℝ), budgetIntegrand g t u) =
      (∫ u in Ioc (0 : ℝ) (2 * r / 3), budgetIntegrand g t u) +
        ∫ u in Ioi (2 * r / 3), budgetIntegrand g t u := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hs0.le,
      setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hF.mono_set (fun u hu => hu.1))
        (hF.mono_set (fun u hu => lt_trans hs0 hu))]
  have hs2 : (∫ u in Ioi (2 * r / 3), budgetIntegrand g t u) =
      (∫ u in Ioc (2 * r / 3) t, budgetIntegrand g t u) + ∫ u in Ioi t, budgetIntegrand g t u := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hst.le,
      setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hF.mono_set (fun u hu => lt_trans hs0 hu.1))
        (hF.mono_set (fun u hu => lt_trans ht0 hu))]
  have hs3 : (∫ u in Ioi t, budgetIntegrand g t u) =
      (∫ u in Ioc t r, budgetIntegrand g t u) + ∫ u in Ioi r, budgetIntegrand g t u := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi htr,
      setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hF.mono_set (fun u hu => lt_trans ht0 hu.1))
        (hF.mono_set (fun u hu => lt_trans hr0 hu))]
  have hs4 : (∫ u in Ioi r, budgetIntegrand g t u) =
      (∫ u in Ioc r (2 * r), budgetIntegrand g t u) +
        ∫ u in Ioi (2 * r), budgetIntegrand g t u := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi (by linarith : r ≤ 2 * r),
      setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hF.mono_set (fun u hu => lt_trans hr0 hu.1))
        (hF.mono_set (fun u hu => by
          change 2 * r < u at hu; change (0 : ℝ) < u; linarith))]
  rw [arch_eq_budget_integral g t hm, hs1, hs2, hs3, hs4, tail_integral_eq_t g t r a hr0 hw]
  have hA := inner_integral_le_s g t (2 * r / 3) hs0 hst.le
  have hB := upper_integral_le g t r a hw hs0 hst.le hexp
  have hC := lower_integral_le g t r a hw ht0 htr hst (by linarith)
  have hD := half_integral_le_bonus g t r a ht0 htr hr1 hw
  unfold cellArch
  nlinarith

/-- **Three-cell diagonal.** -/
theorem cell_diagonal (g : WeilCompactSmoothGV1) (t r a : ℝ) (hr0 : 0 < r)
    (hst : 2 * r / 3 < t) (htr : t ≤ r) (hr1 : 2 * r ≤ 1)
    (hexp : Real.exp (t / 2) ≤ 13 / 12) (hlog : 2 * r < Real.log 2)
    (hw : HalfWidthAt g r a) (hm : WeilMomentConditionsV1 g) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ cellGain t r * energy g.1 := by
  have hp := prime_sum_zero_of_halfWidth g r a hw hlog
  have hb := arch_cell_budget g t r a hr0 hst htr hr1 hexp hw hm
  change (B g g).re ≤ _
  rw [actual_diagonal_rhs_decomposition g hp]
  unfold cellGain
  linarith

end AEGIS.RHThreeCellGainV13

#print axioms AEGIS.RHThreeCellGainV13.arch_cell_budget
#print axioms AEGIS.RHThreeCellGainV13.cell_diagonal
