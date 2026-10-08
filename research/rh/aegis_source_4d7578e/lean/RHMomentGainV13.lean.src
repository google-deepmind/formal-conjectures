import RHMomentIdentityV13
import RHMomentPiecesV13
import RHMomentNumericsV13
import RHNarrowSupportPositivityV13
import Mathlib.Tactic

/-!
AEGIS Ω — the moment gain for the narrow-packet diagonal, V13.

For `g : WeilCompactSmoothGV1` with log-support in `[a − r, a + r]`, `r > 0`,
and vanishing moments, write `E = energy g`, `h(u) = e^u · Re A(e^u)` with
`A = WeilAutocorrelationV1 g`, and `λ = lamR r`.  Proved here:

* `arch_moment_budget`:
  `Re Arch(A) ≤ E · (cothTail(2r) − 2 cothTail r + (r/2) e^{r/2} + 4 (cosh(r/2) − 1))`.
  Route: subtract `λ · ∫_{u>0} h(u)(1 + e^{−u}) = 0` (moment identity), split at
  `r` and `2r`, bound the kernel `1/sinh u − λ(1 + e^{−u})` by its sign on each
  piece together with `|h(u)| ≤ e^{u/2} E`, and integrate the majorants exactly.
* `moment_diagonal`: if also `2r < log 2`, then
  `Re RHS(A) ≤ momentGain r · E` (the prime sum vanishes).
* `wide_coercive`: at `r = 1/8`, `Re RHS(A) ≤ −E/5`.
* `wide_zero_quadratic_nonnegative`, `universal_on_wide_class`: for every
  moment-zero packet of log-half-width `≤ 1/8`, the canonical zero quadratic
  `Re Σ_ρ WeilZeroIndexSummandV1 A ρ` is `≥ 0` (via the repository's explicit
  formula bridge).

This is a restricted class (log-support length `≤ 1/4`); it is not the
universal statement over all packets.  Not RH.  AUTHORITY_EFFECT = NONE.
-/

open Set Complex MeasureTheory
open scoped BigOperators ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHMomentGainV13
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilWidthArchBudgetV26
open AEGIS.WeilWidthArchIntegralV27
open AEGIS.WeilDiagonalKernelReductionV21
open AEGIS.WeilThreeBlockAnalyticConstantsV21
open AEGIS.WeilAutocorrelationExplicitFormulaV10
open AEGIS.RHDyadicDiagonalV13
open AEGIS.RHMomentIdentityV13
open AEGIS.RHMomentPiecesV13
open AEGIS.RHMomentNumericsV13

/-- The weighted moment integrand `h(u)(1 + e^{-u})`. -/
def momentLog (g : WeilCompactSmoothGV1) (u : ℝ) : ℝ :=
  Real.exp u * (WeilAutocorrelationV1 g (Real.exp u)).re * (1 + Real.exp (-u))

/-- The Archimedean log-integrand minus `λ` times the moment integrand. -/
def budgetIntegrand (g : WeilCompactSmoothGV1) (r u : ℝ) : ℝ :=
  widthArchLogIntegrandV26 g u - lamR r * momentLog g u

theorem budgetIntegrand_integrableOn (g : WeilCompactSmoothGV1) (r : ℝ) :
    IntegrableOn (budgetIntegrand g r) (Ioi (0 : ℝ)) :=
  (width_arch_log_integrableOn_v27 g).sub ((moment_log_integrableOn g).const_mul (lamR r))

theorem arch_eq_budget_integral (g : WeilCompactSmoothGV1) (r : ℝ)
    (hm : WeilMomentConditionsV1 g) :
    (WeilArchimedeanIntegralV1 (WeilAutocorrelationV1 g)).re =
      ∫ u in Ioi (0 : ℝ), budgetIntegrand g r u := by
  rw [archimedean_real_eq_log_integral_v27]
  unfold budgetIntegrand momentLog
  rw [integral_sub (width_arch_log_integrableOn_v27 g)
      ((moment_log_integrableOn g).const_mul (lamR r)), integral_const_mul,
    moment_log_identity g hm]
  ring

/-- `e^{u/2} (1 + e^{-u}) = 2 cosh(u/2)`. -/
theorem exp_half_mul (u : ℝ) :
    Real.exp (u / 2) * (1 + Real.exp (-u)) = 2 * Real.cosh (u / 2) := by
  have h : Real.exp (u / 2) * Real.exp (-u) = Real.exp (-(u / 2)) := by
    rw [← Real.exp_add]; ring_nf
  rw [Real.cosh_eq, mul_add, mul_one, h]
  ring

theorem budget_split_form (g : WeilCompactSmoothGV1) (r u : ℝ) :
    budgetIntegrand g r u =
      Real.exp u * (WeilAutocorrelationV1 g (Real.exp u)).re *
          (1 / Real.sinh u - lamR r * (1 + Real.exp (-u))) -
        energy g.1 * (1 / Real.sinh u) := by
  unfold budgetIntegrand momentLog widthArchLogIntegrandV26
  ring

/-- Pointwise majorant on `(0, r]`. -/
theorem inner_majorant (g : WeilCompactSmoothGV1) (r u : ℝ) (hu0 : 0 < u) (hur : u ≤ r) :
    budgetIntegrand g r u ≤
      energy g.1 * (Real.exp (r / 2) / 2) - 2 * lamR r * energy g.1 * Real.cosh (u / 2) := by
  have hE := energy_nonnegative g.1
  have hk := kernel_nonneg r u hu0 hur
  have hh := autocorrelation_exp_re_le_v26 g u
  have h1 := mul_le_mul_of_nonneg_right hh hk
  have h3 := mul_le_mul_of_nonneg_left (inner_pointwise r u hu0 hur) hE
  have h4 := exp_half_mul u
  have hsu : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu0
  have h2 : Real.exp (u / 2) * energy g.1 * (1 / Real.sinh u - lamR r * (1 + Real.exp (-u))) -
      energy g.1 * (1 / Real.sinh u) =
      energy g.1 * ((Real.exp (u / 2) - 1) / Real.sinh u) -
        lamR r * energy g.1 * (Real.exp (u / 2) * (1 + Real.exp (-u))) := by
    field_simp
    ring
  rw [h4] at h2
  rw [budget_split_form]
  linarith

/-- Pointwise majorant on `(r, 2r]` (valid for all `u ≥ r`). -/
theorem middle_majorant (g : WeilCompactSmoothGV1) (r u : ℝ) (hr0 : 0 < r) (hru : r ≤ u) :
    budgetIntegrand g r u ≤
      2 * lamR r * energy g.1 * Real.cosh (u / 2) - 2 * energy g.1 * (1 / Real.sinh u) := by
  have hE := energy_nonnegative g.1
  have hu0 : 0 < u := lt_of_lt_of_le hr0 hru
  have hsu : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu0
  have hk := kernel_nonpos r u hr0 hru
  have hnorm := autocorrelation_exp_norm_le_v26 g u
  have hre : -‖WeilAutocorrelationV1 g (Real.exp u)‖ ≤
      (WeilAutocorrelationV1 g (Real.exp u)).re :=
    le_trans (neg_le_neg (Complex.abs_re_le_norm _)) (neg_abs_le _)
  have hexp : Real.exp u * Real.exp (-u / 2) = Real.exp (u / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hh : -(Real.exp (u / 2) * energy g.1) ≤
      Real.exp u * (WeilAutocorrelationV1 g (Real.exp u)).re := by
    have hpos := Real.exp_pos u
    have := mul_le_mul_of_nonneg_left (le_trans (neg_le_neg hnorm) hre) hpos.le
    rw [mul_neg, ← mul_assoc, hexp] at this
    exact this
  have h1 := mul_le_mul_of_nonpos_right hh hk
  have h4 := exp_half_mul u
  have hge : 0 ≤ energy g.1 * ((Real.exp (u / 2) - 1) / Real.sinh u) := by
    apply mul_nonneg hE (div_nonneg _ hsu.le)
    linarith [Real.one_le_exp (by linarith : (0 : ℝ) ≤ u / 2)]
  have h2 : -(Real.exp (u / 2) * energy g.1) *
        (1 / Real.sinh u - lamR r * (1 + Real.exp (-u))) - energy g.1 * (1 / Real.sinh u) =
      lamR r * energy g.1 * (Real.exp (u / 2) * (1 + Real.exp (-u))) -
        2 * energy g.1 * (1 / Real.sinh u) -
        energy g.1 * ((Real.exp (u / 2) - 1) / Real.sinh u) := by
    field_simp
    ring
  rw [h4] at h2
  rw [budget_split_form]
  linarith

theorem integrableOn_inv_sinh_Ioc (a b : ℝ) (ha : 0 < a) :
    IntegrableOn (fun u : ℝ => 1 / Real.sinh u) (Ioc a b) := by
  have hc : ContinuousOn (fun u : ℝ => 1 / Real.sinh u) (Icc a b) := by
    apply continuousOn_const.div Real.continuous_sinh.continuousOn
    intro u hu
    exact ne_of_gt (Real.sinh_pos_iff.mpr (lt_of_lt_of_le ha hu.1))
  exact (hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self

theorem cosh_half_integrableOn (a b : ℝ) :
    IntegrableOn (fun u : ℝ => Real.cosh (u / 2)) (Ioc a b) :=
  (Real.continuous_cosh.comp (continuous_id.div_const 2)).integrableOn_Ioc

theorem inner_integral_le (g : WeilCompactSmoothGV1) (r : ℝ) (hr0 : 0 < r) :
    (∫ u in Ioc (0 : ℝ) r, budgetIntegrand g r u) ≤
      energy g.1 * ((r / 2) * Real.exp (r / 2)) -
        4 * lamR r * energy g.1 * Real.sinh (r / 2) := by
  have hI : IntegrableOn (budgetIntegrand g r) (Ioc (0 : ℝ) r) :=
    (budgetIntegrand_integrableOn g r).mono_set (fun u hu => hu.1)
  have hM : IntegrableOn (fun u : ℝ => energy g.1 * (Real.exp (r / 2) / 2) -
      2 * lamR r * energy g.1 * Real.cosh (u / 2)) (Ioc (0 : ℝ) r) :=
    continuous_const.integrableOn_Ioc.sub
      ((cosh_half_integrableOn 0 r).const_mul (2 * lamR r * energy g.1))
  calc
    _ ≤ ∫ u in Ioc (0 : ℝ) r, (energy g.1 * (Real.exp (r / 2) / 2) -
          2 * lamR r * energy g.1 * Real.cosh (u / 2)) := by
      apply setIntegral_mono_on hI hM measurableSet_Ioc
      intro u hu
      exact inner_majorant g r u hu.1 hu.2
    _ = _ := by
      rw [integral_sub continuous_const.integrableOn_Ioc
          ((cosh_half_integrableOn 0 r).const_mul (2 * lamR r * energy g.1)),
        setIntegral_const, integral_const_mul, integral_cosh_half 0 r hr0.le, smul_eq_mul,
        Real.volume_real_Ioc_of_le hr0.le]
      simp only [zero_div, Real.sinh_zero, sub_zero]
      ring

theorem middle_integral_le (g : WeilCompactSmoothGV1) (r : ℝ) (hr0 : 0 < r) :
    (∫ u in Ioc r (2 * r), budgetIntegrand g r u) ≤
      4 * lamR r * energy g.1 * (Real.sinh r - Real.sinh (r / 2)) -
        2 * energy g.1 * (cothTail r - cothTail (2 * r)) := by
  have hI : IntegrableOn (budgetIntegrand g r) (Ioc r (2 * r)) :=
    (budgetIntegrand_integrableOn g r).mono_set
      (fun u hu => lt_trans hr0 hu.1)
  have hA := (cosh_half_integrableOn r (2 * r)).const_mul (2 * lamR r * energy g.1)
  have hB := (integrableOn_inv_sinh_Ioc r (2 * r) hr0).const_mul (2 * energy g.1)
  calc
    _ ≤ ∫ u in Ioc r (2 * r), (2 * lamR r * energy g.1 * Real.cosh (u / 2) -
          2 * energy g.1 * (1 / Real.sinh u)) := by
      apply setIntegral_mono_on hI (hA.sub hB) measurableSet_Ioc
      intro u hu
      exact middle_majorant g r u hr0 hu.1.le
    _ = _ := by
      rw [integral_sub hA hB, integral_const_mul, integral_const_mul,
        integral_cosh_half r (2 * r) (by linarith),
        integral_inv_sinh_Ioc r (2 * r) hr0 (by linarith)]
      have h2 : 2 * r / 2 = r := by ring
      rw [h2]
      ring

theorem tail_integral_eq (g : WeilCompactSmoothGV1) (r a : ℝ) (hr0 : 0 < r)
    (hw : HalfWidthAt g r a) :
    (∫ u in Ioi (2 * r), budgetIntegrand g r u) = -energy g.1 * cothTail (2 * r) := by
  rw [← tail_eq g r a hr0 hw]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  unfold budgetIntegrand momentLog
  rw [autocorrelation_zero_of_halfWidth g r a u hw hu]
  simp

/-- **Archimedean budget with the moment gain.** -/
theorem arch_moment_budget (g : WeilCompactSmoothGV1) (r a : ℝ) (hr0 : 0 < r)
    (hw : HalfWidthAt g r a) (hm : WeilMomentConditionsV1 g) :
    (WeilArchimedeanIntegralV1 (WeilAutocorrelationV1 g)).re ≤
      energy g.1 * (cothTail (2 * r) - 2 * cothTail r + (r / 2) * Real.exp (r / 2) +
        4 * (Real.cosh (r / 2) - 1)) := by
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
  have hmid := middle_integral_le g r hr0
  have hlam := mul_le_mul_of_nonneg_left (lam_term_le r hr0) (energy_nonnegative g.1)
  nlinarith

/-- **The moment diagonal.**  Below `log 2` the prime sum vanishes and the
diagonal is bounded by `momentGain r · E`. -/
theorem moment_diagonal (g : WeilCompactSmoothGV1) (r a : ℝ) (hr0 : 0 < r)
    (hlog : 2 * r < Real.log 2) (hw : HalfWidthAt g r a) (hm : WeilMomentConditionsV1 g) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ momentGain r * energy g.1 := by
  have hp := prime_sum_zero_of_halfWidth g r a hw hlog
  have hb := arch_moment_budget g r a hr0 hw hm
  change (B g g).re ≤ _
  rw [actual_diagonal_rhs_decomposition g hp]
  have heq : momentGain r * energy g.1 = diagonalKappaV21 * energy g.1 +
      energy g.1 * (cothTail (2 * r) - 2 * cothTail r + (r / 2) * Real.exp (r / 2) +
        4 * (Real.cosh (r / 2) - 1)) := by
    unfold momentGain; ring
  rw [heq]
  linarith

/-- **Coercivity at log-half-width `1/8`.** -/
theorem wide_coercive (g : WeilCompactSmoothGV1) (a : ℝ) (hw : HalfWidthAt g (1 / 8) a)
    (hm : WeilMomentConditionsV1 g) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ -(1 / 5) * energy g.1 := by
  have hlog : 2 * (1 / 8 : ℝ) < Real.log 2 := by linarith [log_two_lower]
  have hd := moment_diagonal g (1 / 8) a (by norm_num) hlog hw hm
  have hg := mul_le_mul_of_nonneg_right momentGain_eighth (energy_nonnegative g.1)
  linarith

theorem wide_zero_quadratic_nonnegative (g : WeilCompactSmoothGV1) (r a : ℝ) (hr0 : 0 < r)
    (hr : r ≤ 1 / 8) (hw : HalfWidthAt g r a) (hm : WeilMomentConditionsV1 g) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
          WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  have hw8 : HalfWidthAt g (1 / 8) a := by
    intro t ht
    have := hw ht
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hc := wide_coercive g a hw8 hm
  have hE := energy_nonnegative g.1
  exact (autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10 g hm).mp
    (by linarith)

theorem universal_on_wide_class (a : ℝ) :
    ∀ g : WeilCompactSmoothGV1, HalfWidthAt g (1 / 8) a → WeilMomentConditionsV1 g →
      0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
            WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re :=
  fun g hw hm => wide_zero_quadratic_nonnegative g (1 / 8) a (by norm_num) le_rfl hw hm

end AEGIS.RHMomentGainV13

#print axioms AEGIS.RHMomentGainV13.arch_moment_budget
#print axioms AEGIS.RHMomentGainV13.moment_diagonal
#print axioms AEGIS.RHMomentGainV13.wide_coercive
#print axioms AEGIS.RHMomentGainV13.wide_zero_quadratic_nonnegative
#print axioms AEGIS.RHMomentGainV13.universal_on_wide_class
