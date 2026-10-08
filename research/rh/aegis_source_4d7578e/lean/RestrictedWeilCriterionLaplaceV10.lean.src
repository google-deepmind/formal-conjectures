import ZeroHeightShellMassV1
import RestrictedWeilCriterionZeroKernelV10
import WeilAutocorrelationMellinV11
import WeilAutocorrelationClosureV1
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Tactic

/-!
AEGIS Ω — restricted Weil criterion Laplace/Cauchy bridge V10.

Let
  z_rho = 1/2 - rho
and
  a_rho(g) = m_rho * M(Autocorrelation g)(rho).

The translated zero kernel already proved in
`RestrictedWeilCriterionZeroKernelV10` is

  K_g(d) = sum_rho a_rho(g) exp(z_rho d).

This module takes its one-sided Laplace transform.  On Re(w)>1/2 every
individual term is absolutely integrable because all nontrivial zeros lie in
0<Re(rho)<1, hence Re(z_rho)<1/2.  Existing absolute zero-summability gives the
sum/integral exchange and therefore

  Laplace(K_g)(w)
    = sum_rho a_rho(g) / (w - z_rho).

This is the right-half-plane seed identity for the meromorphic continuation
and residue contradiction.  No RH conclusion is asserted here.

AUTHORITY_EFFECT = NONE.
-/

open Set Filter Complex MeasureTheory
open scoped BigOperators Topology

set_option autoImplicit false
noncomputable section

namespace AEGIS.RestrictedWeilCriterionLaplaceV10

/-- The nontrivial zeros form a countable type: they are the union of the
finite canonical height shells. -/
instance countable_nontrivialZeroIndex_v10 :
    Countable RiemannNontrivialZeroIndexV2 := by
  have hU : (Set.univ : Set RiemannNontrivialZeroIndexV2) =
      ⋃ n : ℕ, ZeroHeightShellSetV1 n := by
    ext rho
    simp [ZeroHeightShellSetV1]
  have hc : (Set.univ : Set RiemannNontrivialZeroIndexV2).Countable := by
    rw [hU]
    exact Set.countable_iUnion (fun n => (zero_height_shell_finite_v1 n).countable)
  exact Set.countable_univ_iff.mp hc

open AEGIS.RestrictedWeilCriterionZeroKernelV10
open AEGIS.RestrictedWeilCriterionKernelBridgeV10
open AEGIS.WeilAutocorrelationMellinV11

/-- Multiplicity-weighted autocorrelation coefficient attached to a zero. -/
def ZeroCoefficientV10
    (g : WeilCompactSmoothGV1)
    (rho : RiemannNontrivialZeroIndexV2) : ℂ :=
  (analyticOrderNatAt riemannZeta rho.1 : ℂ) *
    mellin (WeilAutocorrelationV1 g) rho.1

/-- Centered Cauchy summand. -/
def ZeroCauchySummandV10
    (g : WeilCompactSmoothGV1) (w : ℂ)
    (rho : RiemannNontrivialZeroIndexV2) : ℂ :=
  ZeroCoefficientV10 g rho /
    (w - CenteredZeroExponentV10 rho)

/-- Canonical centered Cauchy transform. -/
def ZeroCauchyTransformV10
    (g : WeilCompactSmoothGV1) (w : ℂ) : ℂ :=
  ∑' rho : RiemannNontrivialZeroIndexV2,
    ZeroCauchySummandV10 g w rho

/-- One Laplace-transformed zero-kernel term before integration. -/
def LaplaceZeroTermV10
    (g : WeilCompactSmoothGV1) (w : ℂ)
    (rho : RiemannNontrivialZeroIndexV2) (d : ℝ) : ℂ :=
  Complex.exp (-(w * (d : ℂ))) *
    TranslatedZeroSummandV10 g d rho

/-- One-sided Laplace transform of the actual translated zero kernel. -/
def ZeroKernelLaplaceV10
    (g : WeilCompactSmoothGV1) (w : ℂ) : ℂ :=
  ∫ d : ℝ in Ioi (0 : ℝ),
    Complex.exp (-(w * (d : ℂ))) *
      TranslatedZeroKernelV10 g d

theorem centered_zero_re_lt_half_v10
    (rho : RiemannNontrivialZeroIndexV2) :
    (CenteredZeroExponentV10 rho).re < 1 / 2 := by
  have hstrip :=
    riemann_zeta_nontrivial_zero_critical_strip_v1
      rho.2.1 rho.2.2
  unfold CenteredZeroExponentV10
  simp
  linarith [hstrip.1]

theorem centered_zero_re_gt_neg_half_v10
    (rho : RiemannNontrivialZeroIndexV2) :
    -(1 / 2 : ℝ) < (CenteredZeroExponentV10 rho).re := by
  have hstrip :=
    riemann_zeta_nontrivial_zero_critical_strip_v1
      rho.2.1 rho.2.2
  unfold CenteredZeroExponentV10
  simp
  linarith [hstrip.2]

/-- The Laplace integrand of one zero is exactly one exponential with exponent
z_rho-w. -/
theorem laplace_zero_term_eq_v10
    (g : WeilCompactSmoothGV1) (w : ℂ)
    (rho : RiemannNontrivialZeroIndexV2) (d : ℝ) :
    LaplaceZeroTermV10 g w rho d =
      ZeroCoefficientV10 g rho *
        Complex.exp
          ((CenteredZeroExponentV10 rho - w) * (d : ℂ)) := by
  unfold LaplaceZeroTermV10 ZeroCoefficientV10
  rw [translated_zero_summand_eq_centered_exp_v10]
  have hsplit :
      Complex.exp ((CenteredZeroExponentV10 rho - w) * (d : ℂ)) =
        Complex.exp (-(w * (d : ℂ))) *
          Complex.exp (CenteredZeroExponentV10 rho * (d : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hsplit]
  ring

/-- Individual Laplace terms are integrable on Re(w)>1/2. -/
theorem laplace_zero_term_integrable_v10
    (g : WeilCompactSmoothGV1) {w : ℂ}
    (hw : 1 / 2 < w.re)
    (rho : RiemannNontrivialZeroIndexV2) :
    IntegrableOn
      (LaplaceZeroTermV10 g w rho)
      (Ioi (0 : ℝ)) := by
  have hrate :
      (CenteredZeroExponentV10 rho - w).re < 0 := by
    have hz := centered_zero_re_lt_half_v10 rho
    simp
    linarith
  have hexp :=
    integrableOn_exp_mul_complex_Ioi
      (a := CenteredZeroExponentV10 rho - w)
      hrate 0
  refine IntegrableOn.congr_fun
    (hexp.const_mul (ZeroCoefficientV10 g rho))
    (fun d hd => ?_) measurableSet_Ioi
  rw [laplace_zero_term_eq_v10]

/-- Exact integral of one Laplace zero term. -/
theorem integral_laplace_zero_term_v10
    (g : WeilCompactSmoothGV1) {w : ℂ}
    (hw : 1 / 2 < w.re)
    (rho : RiemannNontrivialZeroIndexV2) :
    (∫ d : ℝ in Ioi (0 : ℝ),
      LaplaceZeroTermV10 g w rho d) =
      ZeroCauchySummandV10 g w rho := by
  have hrate :
      (CenteredZeroExponentV10 rho - w).re < 0 := by
    have hz := centered_zero_re_lt_half_v10 rho
    simp
    linarith
  have hneq :
      w - CenteredZeroExponentV10 rho ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    have hz := centered_zero_re_lt_half_v10 rho
    linarith
  rw [show
    (fun d : ℝ => LaplaceZeroTermV10 g w rho d) =
      (fun d : ℝ =>
        ZeroCoefficientV10 g rho *
          Complex.exp
            ((CenteredZeroExponentV10 rho - w) * (d : ℂ))) by
              funext d
              exact laplace_zero_term_eq_v10 g w rho d,
    integral_const_mul,
    integral_exp_mul_complex_Ioi hrate 0]
  unfold ZeroCauchySummandV10
  have hneq' : -w + CenteredZeroExponentV10 rho ≠ 0 := by
    intro h
    apply hneq
    linear_combination -h
  simp
  rw [div_eq_mul_one_div]
  congr 1
  rw [show CenteredZeroExponentV10 rho - w = -(w - CenteredZeroExponentV10 rho) by ring,
    one_div, inv_neg]
  ring

/-- Existing compact-smooth zero summability gives summability of the
coefficient norms used in the Cauchy transform. -/
theorem zero_coefficient_norm_summable_v10
    (g : WeilCompactSmoothGV1) :
    Summable (fun rho : RiemannNontrivialZeroIndexV2 =>
      ‖ZeroCoefficientV10 g rho‖) := by
  have h :=
    weil_compact_smooth_zero_norm_summable_v1
      (WeilAutocorrelationCompactSmoothV1 g)
  refine h.congr (fun rho => ?_)
  rfl

/-- Exact norm integral for one term. -/
theorem integral_norm_laplace_zero_term_v10
    (g : WeilCompactSmoothGV1) {w : ℂ}
    (hw : 1 / 2 < w.re)
    (rho : RiemannNontrivialZeroIndexV2) :
    (∫ d : ℝ in Ioi (0 : ℝ),
      ‖LaplaceZeroTermV10 g w rho d‖) =
      ‖ZeroCoefficientV10 g rho‖ /
        (w.re - (CenteredZeroExponentV10 rho).re) := by
  have hrate :
      (CenteredZeroExponentV10 rho).re - w.re < 0 := by
    have hz := centered_zero_re_lt_half_v10 rho
    linarith
  have hden :
      0 < w.re - (CenteredZeroExponentV10 rho).re := by
    linarith
  have hfun :
      (fun d : ℝ =>
        ‖LaplaceZeroTermV10 g w rho d‖) =
      (fun d : ℝ =>
        ‖ZeroCoefficientV10 g rho‖ *
          Real.exp
            (((CenteredZeroExponentV10 rho).re - w.re) * d)) := by
    funext d
    rw [laplace_zero_term_eq_v10]
    rw [norm_mul, Complex.norm_exp]
    congr 1
    simp
  rw [hfun, integral_const_mul,
    integral_exp_mul_Ioi hrate 0]
  rw [mul_zero, Real.exp_zero, div_eq_mul_one_div (‖ZeroCoefficientV10 g rho‖)]
  congr 1
  rw [neg_div, ← div_neg, neg_sub]

/-- The integrals of term norms are summable uniformly on each fixed
right-half-plane point Re(w)>1/2. -/
theorem laplace_zero_term_integral_norm_summable_v10
    (g : WeilCompactSmoothGV1) {w : ℂ}
    (hw : 1 / 2 < w.re) :
    Summable (fun rho : RiemannNontrivialZeroIndexV2 =>
      ∫ d : ℝ in Ioi (0 : ℝ),
        ‖LaplaceZeroTermV10 g w rho d‖) := by
  let delta : ℝ := w.re - 1 / 2
  have hdelta : 0 < delta := by
    dsimp [delta]
    linarith
  have hcoef := zero_coefficient_norm_summable_v10 g
  have hmajor :
      Summable (fun rho : RiemannNontrivialZeroIndexV2 =>
        ‖ZeroCoefficientV10 g rho‖ * (1 / delta)) :=
    hcoef.mul_right (1 / delta)
  refine Summable.of_nonneg_of_le
    (fun rho => integral_nonneg (fun _ => norm_nonneg _))
    (fun rho => ?_) hmajor
  rw [integral_norm_laplace_zero_term_v10 g hw rho]
  have hz := centered_zero_re_lt_half_v10 rho
  have hden :
      delta ≤ w.re - (CenteredZeroExponentV10 rho).re := by
    dsimp [delta]
    linarith
  have hrecip :
      1 / (w.re - (CenteredZeroExponentV10 rho).re) ≤
        1 / delta :=
    one_div_le_one_div_of_le hdelta hden
  rw [div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left hrecip (norm_nonneg _)

/-- On Re(w)>1/2, sum/integral exchange is justified by absolute
integrability. -/
theorem laplace_zero_terms_hasSum_integral_v10
    (g : WeilCompactSmoothGV1) {w : ℂ}
    (hw : 1 / 2 < w.re) :
    HasSum
      (fun rho : RiemannNontrivialZeroIndexV2 =>
        ∫ d : ℝ in Ioi (0 : ℝ),
          LaplaceZeroTermV10 g w rho d)
      (∫ d : ℝ in Ioi (0 : ℝ),
        ∑' rho : RiemannNontrivialZeroIndexV2,
          LaplaceZeroTermV10 g w rho d) := by
  exact hasSum_integral_of_summable_integral_norm
    (fun rho => laplace_zero_term_integrable_v10 g hw rho)
    (laplace_zero_term_integral_norm_summable_v10 g hw)

/-- Pointwise, multiplying the translated kernel by the Laplace exponential
is the tsum of the individual Laplace terms. -/
theorem laplace_kernel_eq_tsum_terms_v10
    (g : WeilCompactSmoothGV1) (w : ℂ) (d : ℝ) :
    Complex.exp (-(w * (d : ℂ))) *
        TranslatedZeroKernelV10 g d =
      ∑' rho : RiemannNontrivialZeroIndexV2,
        LaplaceZeroTermV10 g w rho d := by
  unfold TranslatedZeroKernelV10 LaplaceZeroTermV10
  rw [tsum_mul_left]

/-- Measurability of the translated zero kernel, obtained from its centered
exponential tsum representation. -/
theorem translated_zero_kernel_measurable_v10
    (g : WeilCompactSmoothGV1) :
    Measurable (TranslatedZeroKernelV10 g) := by
  have hfun :
      TranslatedZeroKernelV10 g =
      fun d : ℝ =>
          ∑' rho : RiemannNontrivialZeroIndexV2,
            (analyticOrderNatAt riemannZeta rho.1 : ℂ) *
              (Complex.exp
                (CenteredZeroExponentV10 rho * (d : ℂ)) *
                mellin (WeilAutocorrelationV1 g) rho.1) := by
    funext d
    exact translated_zero_kernel_eq_centered_exp_tsum_v10 g d
  rw [hfun]
  apply Measurable.tsum
  intro rho
  fun_prop

/-- Under the universal sign hypothesis, the one-sided Laplace integrand is
absolutely integrable for every Re(w)>0. -/
theorem zero_kernel_laplace_integrable_v10
    (hU : AEGIS.RHMillenniumGateV10.UniversalZeroQuadraticNonnegativeV10)
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn
      (fun d : ℝ =>
        Complex.exp (-(w * (d : ℂ))) *
          TranslatedZeroKernelV10 g d)
      (Ioi (0 : ℝ)) := by
  let C : ℝ := 2 * TranslatedArithmeticDiagonalV10 g
  have hK :=
    universal_zero_quadratic_implies_zero_kernel_bounded_v10
      hU g hm
  have hC : 0 ≤ C := by
    have h0 := hK 0
    exact (norm_nonneg (TranslatedZeroKernelV10 g 0)).trans h0
  have htail :
      IntegrableOn
        (fun d : ℝ => C * Real.exp (-(w.re * d)))
        (Ioi (0 : ℝ)) := by
    have he :=
      integrableOn_exp_mul_Ioi
        (a := -w.re) (by linarith) 0
    have h2 := he.const_mul C
    simp only [neg_mul] at h2
    exact h2
  refine htail.mono' ?_ ?_
  · have hKmeas :=
      (translated_zero_kernel_measurable_v10 g).aestronglyMeasurable
        (μ := volume.restrict (Ioi (0 : ℝ)))
    have hEmeas :
        AEStronglyMeasurable
          (fun d : ℝ => Complex.exp (-(w * (d : ℂ))))
          (volume.restrict (Ioi (0 : ℝ))) := by
      exact (by fun_prop : Continuous
        (fun d : ℝ => Complex.exp (-(w * (d : ℂ))))).aestronglyMeasurable
    exact hEmeas.mul hKmeas
  · rw [ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall (fun d hd => by
      have hKd := hK d
      rw [norm_mul, Complex.norm_exp]
      have hre :
          (-(w * (d : ℂ))).re = -(w.re * d) := by
            simp
      rw [hre]
      have hexp : 0 ≤ Real.exp (-(w.re * d)) :=
        (Real.exp_pos _).le
      rw [mul_comm C]
      exact mul_le_mul_of_nonneg_left hKd hexp)

/-- Derivative of the Laplace transform on the full right half-plane.
The proof is a local dominated-differentiation argument exactly analogous to
Mathlib's complex moment-generating-function proof. -/
theorem hasDerivAt_zero_kernel_laplace_v10
    (hU : AEGIS.RHMillenniumGateV10.UniversalZeroQuadraticNonnegativeV10)
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt
      (ZeroKernelLaplaceV10 g)
      (∫ d : ℝ in Ioi (0 : ℝ),
        (Complex.exp (-(w * (d : ℂ))) * (-(d : ℂ))) *
          TranslatedZeroKernelV10 g d)
      w := by
  let C : ℝ := 2 * TranslatedArithmeticDiagonalV10 g
  let r : ℝ := w.re / 2
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hK :=
    universal_zero_quadratic_implies_zero_kernel_bounded_v10
      hU g hm
  have hC : 0 ≤ C := by
    have h0 := hK 0
    exact (norm_nonneg (TranslatedZeroKernelV10 g 0)).trans h0

  let F : ℂ → ℝ → ℂ := fun z d =>
    Complex.exp (-(z * (d : ℂ))) *
      TranslatedZeroKernelV10 g d
  let F' : ℂ → ℝ → ℂ := fun z d =>
    (Complex.exp (-(z * (d : ℂ))) * (-(d : ℂ))) *
      TranslatedZeroKernelV10 g d
  let bound : ℝ → ℝ := fun d =>
    C * d * Real.exp (-(r * d))

  have hFmeas :
      ∀ᶠ z in 𝓝 w,
        AEStronglyMeasurable
          (F z) (volume.restrict (Ioi (0 : ℝ))) := by
    exact Filter.Eventually.of_forall (fun z => by
      have hKmeas :=
        (translated_zero_kernel_measurable_v10 g).aestronglyMeasurable
          (μ := volume.restrict (Ioi (0 : ℝ)))
      have hEmeas :
          AEStronglyMeasurable
            (fun d : ℝ => Complex.exp (-(z * (d : ℂ))))
            (volume.restrict (Ioi (0 : ℝ))) := by
        exact (by fun_prop : Continuous
          (fun d : ℝ => Complex.exp (-(z * (d : ℂ))))).aestronglyMeasurable
      exact hEmeas.mul hKmeas)

  have hFint :
      Integrable (F w) (volume.restrict (Ioi (0 : ℝ))) := by
    exact zero_kernel_laplace_integrable_v10 hU g hm hw

  have hF'meas :
      AEStronglyMeasurable
        (F' w) (volume.restrict (Ioi (0 : ℝ))) := by
    have hKmeas :=
      (translated_zero_kernel_measurable_v10 g).aestronglyMeasurable
        (μ := volume.restrict (Ioi (0 : ℝ)))
    have hEmeas :
        AEStronglyMeasurable
          (fun d : ℝ =>
            Complex.exp (-(w * (d : ℂ))) * (-(d : ℂ)))
          (volume.restrict (Ioi (0 : ℝ))) := by
      exact (by fun_prop : Continuous
        (fun d : ℝ =>
          Complex.exp (-(w * (d : ℂ))) * (-(d : ℂ)))).aestronglyMeasurable
    exact hEmeas.mul hKmeas

  have hboundInt :
      Integrable bound (volume.restrict (Ioi (0 : ℝ))) := by
    have hbase :
        IntegrableOn
          (fun d : ℝ => d * Real.exp (-(r * d)))
          (Ioi (0 : ℝ)) := by
      have hI :=
        integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := r)
          (by norm_num) (by norm_num) hr
      refine hI.congr_fun (fun d _ => ?_) measurableSet_Ioi
      simp [Real.rpow_one]
    simpa [bound, mul_assoc] using hbase.const_mul C

  have hbound :
      ∀ᵐ d ∂(volume.restrict (Ioi (0 : ℝ))),
        ∀ z ∈ Metric.ball w r, ‖F' z d‖ ≤ bound d := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall (fun d hd z hz => by
      have hd0 : 0 < d := hd
      have hdist : ‖z - w‖ < r := by
        simpa [Metric.mem_ball, dist_eq_norm] using hz
      have hreabs : |z.re - w.re| ≤ ‖z - w‖ := by
        simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - w)
      have hzre : r < z.re := by
        have hlow := (abs_lt.mp (lt_of_le_of_lt hreabs hdist)).1
        dsimp [r] at hlow ⊢
        linarith
      have hKd := hK d
      dsimp [F', bound]
      rw [norm_mul, norm_mul, Complex.norm_exp, norm_neg,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd0]
      have hre :
          (-(z * (d : ℂ))).re = -(z.re * d) := by
            simp
      rw [hre]
      have hexp :
          Real.exp (-(z.re * d)) ≤ Real.exp (-(r * d)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      calc
        Real.exp (-(z.re * d)) * d *
            ‖TranslatedZeroKernelV10 g d‖
          ≤ Real.exp (-(z.re * d)) * d * C := by
              gcongr
        _ ≤ Real.exp (-(r * d)) * d * C := by
              gcongr
        _ = C * d * Real.exp (-(r * d)) := by ring)

  have hdiff :
      ∀ᵐ d ∂(volume.restrict (Ioi (0 : ℝ))),
        ∀ z ∈ Metric.ball w r,
          HasDerivAt (F · d) (F' z d) z := by
    exact Filter.Eventually.of_forall (fun d z hz => by
      have hinner :
          HasDerivAt
            (fun q : ℂ => -(q * (d : ℂ)))
            (-(d : ℂ)) z := by
        exact (hasDerivAt_mul_const (d : ℂ)).neg
      have he := hinner.cexp
      have hm :=
        he.mul_const (TranslatedZeroKernelV10 g d)
      simpa [F, F', mul_assoc] using hm)

  have main :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Ioi (0 : ℝ)))
      (F := F) (F' := F') (bound := bound)
      (Metric.ball_mem_nhds w hr)
      hFmeas hFint hF'meas hbound hboundInt hdiff
  exact main.2

/-- The bounded-kernel Laplace transform is holomorphic throughout Re(w)>0. -/
theorem zero_kernel_laplace_analyticOnNhd_v10
    (hU : AEGIS.RHMillenniumGateV10.UniversalZeroQuadraticNonnegativeV10)
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g) :
    AnalyticOnNhd ℂ (ZeroKernelLaplaceV10 g)
      {w : ℂ | 0 < w.re} := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := by
    exact Complex.continuous_re.isOpen_preimage (Ioi (0 : ℝ)) isOpen_Ioi
  apply DifferentiableOn.analyticOnNhd
  · intro w hw
    exact
      (hasDerivAt_zero_kernel_laplace_v10
        hU g hm hw).differentiableAt.differentiableWithinAt
  · exact hopen

/-- Seed Cauchy identity: the Laplace transform of the translated zero kernel
equals its centered Cauchy transform on Re(w)>1/2. -/
theorem zero_kernel_laplace_eq_cauchy_v10
    (g : WeilCompactSmoothGV1) {w : ℂ}
    (hw : 1 / 2 < w.re) :
    ZeroKernelLaplaceV10 g w =
      ZeroCauchyTransformV10 g w := by
  have hsum :=
    laplace_zero_terms_hasSum_integral_v10 g hw
  unfold ZeroKernelLaplaceV10 ZeroCauchyTransformV10
  calc
    (∫ d : ℝ in Ioi (0 : ℝ),
      Complex.exp (-(w * (d : ℂ))) *
        TranslatedZeroKernelV10 g d)
      =
    ∫ d : ℝ in Ioi (0 : ℝ),
      ∑' rho : RiemannNontrivialZeroIndexV2,
        LaplaceZeroTermV10 g w rho d := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro d hd
          exact laplace_kernel_eq_tsum_terms_v10 g w d
    _ =
      ∑' rho : RiemannNontrivialZeroIndexV2,
        ∫ d : ℝ in Ioi (0 : ℝ),
          LaplaceZeroTermV10 g w rho d :=
      hsum.tsum_eq.symm
    _ =
      ∑' rho : RiemannNontrivialZeroIndexV2,
        ZeroCauchySummandV10 g w rho := by
          apply tsum_congr
          intro rho
          exact integral_laplace_zero_term_v10 g hw rho

end AEGIS.RestrictedWeilCriterionLaplaceV10

#print axioms AEGIS.RestrictedWeilCriterionLaplaceV10.integral_laplace_zero_term_v10
#print axioms AEGIS.RestrictedWeilCriterionLaplaceV10.hasDerivAt_zero_kernel_laplace_v10
#print axioms AEGIS.RestrictedWeilCriterionLaplaceV10.zero_kernel_laplace_analyticOnNhd_v10
#print axioms AEGIS.RestrictedWeilCriterionLaplaceV10.laplace_zero_term_integral_norm_summable_v10
#print axioms AEGIS.RestrictedWeilCriterionLaplaceV10.zero_kernel_laplace_eq_cauchy_v10
