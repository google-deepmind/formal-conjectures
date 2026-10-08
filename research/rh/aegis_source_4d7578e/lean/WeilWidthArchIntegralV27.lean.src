import WeilWidthArchBudgetV26
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
AEGIS Ω — width-1/32 actual Archimedean integral budget V2.7.

This module performs the final integration step above the pointwise V2.6
Archimedean bounds.

1. Substitute x = exp u in the actual repository Archimedean integral.
2. Split (0,∞) into (0,1/32] and (1/32,∞).
3. Integrate the V2.6 inner pointwise majorant exactly.
4. Use the V2.6 exact outer-tail identity and the V2.4 coth tail.
5. Discharge the sole V2.4 Archimedean-budget premise.

The resulting 103/100 diagonal coercive estimate is only for the retained
width-1/32 packet class.  No off-diagonal estimate, global Weil sign, or RH
conclusion is asserted here.
-/

open Set Function MeasureTheory Complex
open scoped ComplexConjugate BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilWidthArchIntegralV27

open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilWidthArchBudgetV26
open AEGIS.WeilDiagonalKernelReductionV21
open AEGIS.WeilWidthDiagonalArchFrontierV24
open AEGIS.WeilMixedAlgebraV2

private def archLogComplexV27
    (g : WeilCompactSmoothGV1) (u : ℝ) : ℂ :=
  Real.exp u •
    WeilArchimedeanIntegrandV1
      (WeilAutocorrelationV1 g) (Real.exp u)

/-- The exponential pullback of the actual Archimedean integrand is
integrable on the positive logarithmic half-line. -/
theorem arch_log_complex_integrableOn_v27
    (g : WeilCompactSmoothGV1) :
    IntegrableOn (archLogComplexV27 g) (Ioi (0 : ℝ)) := by
  have hbase :
      IntegrableOn
        (WeilArchimedeanIntegrandV1 (WeilAutocorrelationV1 g))
        (Ioi (1 : ℝ)) := by
    simpa only [weil_autocorrelation_compact_smooth_coe_v1] using
      (weil_compact_smooth_archimedean_integrable_v1
        (WeilAutocorrelationCompactSmoothV1 g))
  have hpull :=
    (integrableOn_comp_exp_Ioi
      (WeilArchimedeanIntegrandV1 (WeilAutocorrelationV1 g)) 0).2
      (by simpa using hbase)
  change IntegrableOn
    (fun u : ℝ => Real.exp u •
      WeilArchimedeanIntegrandV1
        (WeilAutocorrelationV1 g) (Real.exp u))
    (Ioi (0 : ℝ))
  exact hpull

/-- The real transformed integrand from V2.6 is integrable on (0,∞). -/
theorem width_arch_log_integrableOn_v27
    (g : WeilCompactSmoothGV1) :
    IntegrableOn (widthArchLogIntegrandV26 g) (Ioi (0 : ℝ)) := by
  have hcomplex := arch_log_complex_integrableOn_v27 g
  have hreal :
      IntegrableOn (fun u : ℝ => (archLogComplexV27 g u).re)
        (Ioi (0 : ℝ)) := hcomplex.re
  refine hreal.congr ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  unfold archLogComplexV27
  have hre :
      (Real.exp u •
        WeilArchimedeanIntegrandV1
          (WeilAutocorrelationV1 g) (Real.exp u)).re =
        Real.exp u *
          (WeilArchimedeanIntegrandV1
            (WeilAutocorrelationV1 g) (Real.exp u)).re := by
    simp only [Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hre]
  exact exp_mul_archimedean_re_eq_log_v26 g hu

/-- Exact x=exp(u) conversion for the real part of the actual repository
Archimedean integral. -/
theorem archimedean_real_eq_log_integral_v27
    (g : WeilCompactSmoothGV1) :
    (WeilArchimedeanIntegralV1 (WeilAutocorrelationV1 g)).re =
      ∫ u in Ioi (0 : ℝ), widthArchLogIntegrandV26 g u := by
  let G : ℝ → ℂ :=
    WeilArchimedeanIntegrandV1 (WeilAutocorrelationV1 g)
  have hcomplex := arch_log_complex_integrableOn_v27 g
  change IntegrableOn
    (fun u : ℝ => Real.exp u • G (Real.exp u))
    (Ioi (0 : ℝ)) at hcomplex
  have hchange :
      (∫ u in Ioi (0 : ℝ), Real.exp u • G (Real.exp u)) =
        ∫ x in Ioi (1 : ℝ), G x := by
    simpa using (integral_comp_exp_Ioi G 0)
  unfold WeilArchimedeanIntegralV1
  change (∫ x in Ioi (1 : ℝ), G x).re =
    ∫ u in Ioi (0 : ℝ), widthArchLogIntegrandV26 g u
  calc
    (∫ x in Ioi (1 : ℝ), G x).re =
        (∫ u in Ioi (0 : ℝ), Real.exp u • G (Real.exp u)).re := by
          exact congrArg Complex.re hchange.symm
    _ = ∫ u in Ioi (0 : ℝ),
          (Real.exp u • G (Real.exp u)).re := by
          exact (integral_re hcomplex).symm
    _ = ∫ u in Ioi (0 : ℝ), widthArchLogIntegrandV26 g u := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro u hu
          dsimp [G]
          simpa only [Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, zero_mul, sub_zero] using
            (exp_mul_archimedean_re_eq_log_v26 g hu)

/-- Exact split of the transformed integral at the retained width 1/32. -/
theorem width_arch_log_split_v27
    (g : WeilCompactSmoothGV1) :
    (∫ u in Ioi (0 : ℝ), widthArchLogIntegrandV26 g u) =
      (∫ u in Ioc (0 : ℝ) (1 / 32 : ℝ),
        widthArchLogIntegrandV26 g u) +
      ∫ u in Ioi (1 / 32 : ℝ), widthArchLogIntegrandV26 g u := by
  have hfull := width_arch_log_integrableOn_v27 g
  have hinner :
      IntegrableOn (widthArchLogIntegrandV26 g)
        (Ioc (0 : ℝ) (1 / 32 : ℝ)) :=
    hfull.mono_set (by
      intro u hu
      exact hu.1)
  have htail :
      IntegrableOn (widthArchLogIntegrandV26 g)
        (Ioi (1 / 32 : ℝ)) :=
    hfull.mono_set (by
      intro u hu
      change (1 / 32 : ℝ) < u at hu
      change (0 : ℝ) < u
      linarith)
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1 / 32),
    setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hinner htail]

/-- The inner window integrates to at most diagonalSmallV21 times the packet
energy. -/
theorem width_arch_inner_integral_le_v27
    (g : WeilCompactSmoothGV1) :
    (∫ u in Ioc (0 : ℝ) (1 / 32 : ℝ),
      widthArchLogIntegrandV26 g u) ≤
      energy g.1 * diagonalSmallV21 := by
  let C : ℝ :=
    energy g.1 * (Real.exp (1 / 64 : ℝ) / 2)
  have hfull := width_arch_log_integrableOn_v27 g
  have hinner :
      IntegrableOn (widthArchLogIntegrandV26 g)
        (Ioc (0 : ℝ) (1 / 32 : ℝ)) :=
    hfull.mono_set (by
      intro u hu
      exact hu.1)
  have hconst : IntegrableOn (fun _ : ℝ => C)
      (Ioc (0 : ℝ) (1 / 32 : ℝ)) := by
    exact continuous_const.integrableOn_Ioc
  have hmono :
      (∫ u in Ioc (0 : ℝ) (1 / 32 : ℝ),
        widthArchLogIntegrandV26 g u) ≤
      ∫ _u in Ioc (0 : ℝ) (1 / 32 : ℝ), C := by
    refine setIntegral_mono_on hinner hconst measurableSet_Ioc ?_
    intro u hu
    dsimp [C]
    exact width_arch_log_inner_pointwise_v26 g hu.1 hu.2
  calc
    (∫ u in Ioc (0 : ℝ) (1 / 32 : ℝ),
      widthArchLogIntegrandV26 g u)
        ≤ ∫ _u in Ioc (0 : ℝ) (1 / 32 : ℝ), C := hmono
    _ = (1 / 32 : ℝ) * C := by
      rw [setIntegral_const, smul_eq_mul,
        Real.volume_real_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 32)]
      ring
    _ = energy g.1 * diagonalSmallV21 := by
      dsimp [C]
      unfold diagonalSmallV21
      ring

/-- Outside the retained width, the transformed integral is exactly minus the
packet energy times the V2.4 coth tail. -/
theorem width_arch_tail_integral_eq_v27
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneThirtyTwoAt g a) :
    (∫ u in Ioi (1 / 32 : ℝ), widthArchLogIntegrandV26 g u) =
      -energy g.1 * diagonalTailV24 := by
  calc
    (∫ u in Ioi (1 / 32 : ℝ), widthArchLogIntegrandV26 g u)
        =
      ∫ u in Ioi (1 / 32 : ℝ),
        (-energy g.1) * (1 / Real.sinh u) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro u hu
          rw [width_arch_log_tail_eq_v26 g a hw hu]
          ring
    _ = (-energy g.1) *
        (∫ u in Ioi (1 / 32 : ℝ), 1 / Real.sinh u) := by
          rw [integral_const_mul]
    _ = -energy g.1 * diagonalTailV24 := by
          rfl

/-- The sole V2.4 Archimedean-budget premise is now discharged for every
retained width-1/32 packet. -/
theorem width_archimedean_budget_v27
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneThirtyTwoAt g a) :
    (WeilArchimedeanIntegralV1 (WeilAutocorrelationV1 g)).re ≤
      energy g.1 * (diagonalSmallV21 - diagonalTailV24) := by
  rw [archimedean_real_eq_log_integral_v27,
    width_arch_log_split_v27]
  have hinner := width_arch_inner_integral_le_v27 g
  have htail := width_arch_tail_integral_eq_v27 g a hw
  calc
    (∫ u in Ioc (0 : ℝ) (1 / 32 : ℝ),
        widthArchLogIntegrandV26 g u) +
        ∫ u in Ioi (1 / 32 : ℝ), widthArchLogIntegrandV26 g u
        ≤ energy g.1 * diagonalSmallV21 +
          (-energy g.1 * diagonalTailV24) := by
            exact add_le_add hinner (le_of_eq htail)
    _ = energy g.1 * (diagonalSmallV21 - diagonalTailV24) := by
          ring

/-- Unconditional retained-packet diagonal coercivity: the former Archimedean
budget premise is no longer present. -/
theorem width_diagonal_103_over_100_v27
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneThirtyTwoAt g a) :
    (103 / 100 : ℝ) * energy g.1 ≤ -(B g g).re := by
  exact width_diagonal_103_over_100_of_arch_budget_v24
    g a hw (width_archimedean_budget_v27 g a hw)

end AEGIS.WeilWidthArchIntegralV27

#print axioms AEGIS.WeilWidthArchIntegralV27.arch_log_complex_integrableOn_v27
#print axioms AEGIS.WeilWidthArchIntegralV27.archimedean_real_eq_log_integral_v27
#print axioms AEGIS.WeilWidthArchIntegralV27.width_arch_inner_integral_le_v27
#print axioms AEGIS.WeilWidthArchIntegralV27.width_arch_tail_integral_eq_v27
#print axioms AEGIS.WeilWidthArchIntegralV27.width_archimedean_budget_v27
#print axioms AEGIS.WeilWidthArchIntegralV27.width_diagonal_103_over_100_v27
