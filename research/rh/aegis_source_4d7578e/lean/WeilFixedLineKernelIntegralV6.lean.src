import WeilPairedMellinProfileV5
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
AEGIS Ω — fixed-line Laplace/Mellin kernel integral v6.

This is the machine-checkable KI step from the fixed-line proof note.  For
s=c+it and Re a<c,

  1/(s-a) = ∫_0^∞ exp (-(s-a)v) dv,

and the product with the actual Mellin transform is absolutely integrable on
R_t × (0,∞)_v.  Fubini plus Mellin inversion then yields the exact log-coordinate
kernel identity

  (1/(2π)) ∫_R F(c+it)/(c+it-a) dt
    = ∫_0^∞ exp(a v) f(exp v) dv.

No zero-sum reindexing, gamma/digamma evaluation, explicit-formula assembly,
arithmetic sign, global Weil positivity, or RH conclusion is asserted here.
-/

open Set Filter Topology Complex MeasureTheory
open scoped BigOperators

set_option autoImplicit false

noncomputable section

def WeilFixedLineMellinV6
    (f : WeilCompactSmoothGV1) (c t : ℝ) : ℂ :=
  mellin f.1 ((c : ℂ) + (t : ℂ) * I)

def WeilFixedLineLaplaceKernelV6
    (f : WeilCompactSmoothGV1) (c : ℝ) (a : ℂ) (p : ℝ × ℝ) : ℂ :=
  Complex.exp
      (-((((c : ℂ) + (p.1 : ℂ) * I) - a) * (p.2 : ℂ))) *
    WeilFixedLineMellinV6 f c p.1

private theorem weil_fixed_line_laplace_factor_norm_v6
    (c t v : ℝ) (a : ℂ) :
    ‖Complex.exp
      (-((((c : ℂ) + (t : ℂ) * I) - a) * (v : ℂ)))‖ =
      Real.exp (-((c - a.re) * v)) := by
  rw [Complex.norm_exp]
  congr 1
  simp

/-- The fixed-line Cauchy kernel is a convergent Laplace integral. -/
theorem weil_fixed_line_laplace_kernel_integral_v6
    (c t : ℝ) (a : ℂ) (ha : a.re < c) :
    (∫ v : ℝ in Ioi (0 : ℝ),
      Complex.exp
        (-((((c : ℂ) + (t : ℂ) * I) - a) * (v : ℂ)))) =
      1 / (((c : ℂ) + (t : ℂ) * I) - a) := by
  have hb :
      (-(((c : ℂ) + (t : ℂ) * I) - a)).re < 0 := by
    simp
    linarith
  rw [show
      (fun v : ℝ =>
        Complex.exp (-((((c : ℂ) + (t : ℂ) * I) - a) * (v : ℂ)))) =
      (fun v : ℝ =>
        Complex.exp
          ((-(((c : ℂ) + (t : ℂ) * I) - a)) * (v : ℂ))) by
        funext v
        congr 1
        ring]
  have hden :
      ((c : ℂ) + (t : ℂ) * I) - a ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  rw [integral_exp_mul_complex_Ioi hb 0]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp [hden]

private theorem weil_fixed_line_laplace_kernel_integrable_v6
    (c t : ℝ) (a : ℂ) (ha : a.re < c) :
    IntegrableOn
      (fun v : ℝ =>
        Complex.exp
          (-((((c : ℂ) + (t : ℂ) * I) - a) * (v : ℂ))))
      (Ioi (0 : ℝ)) := by
  have hb :
      (-(((c : ℂ) + (t : ℂ) * I) - a)).re < 0 := by
    simp
    linarith
  rw [show
      (fun v : ℝ =>
        Complex.exp (-((((c : ℂ) + (t : ℂ) * I) - a) * (v : ℂ)))) =
      (fun v : ℝ =>
        Complex.exp
          ((-(((c : ℂ) + (t : ℂ) * I) - a)) * (v : ℂ))) by
        funext v
        congr 1
        ring]
  exact integrableOn_exp_mul_complex_Ioi hb 0

/-- Absolute product-integrability needed for the actual t/v Fubini swap. -/
theorem weil_fixed_line_laplace_mellin_product_integrable_v6
    (f : WeilCompactSmoothGV1) (c : ℝ) (a : ℂ) (ha : a.re < c) :
    Integrable
      (WeilFixedLineLaplaceKernelV6 f c a)
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
  let F : ℝ → ℂ := fun t => WeilFixedLineMellinV6 f c t
  let δ : ℝ := c - a.re
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  have hF : Integrable F := by
    dsimp [F, WeilFixedLineMellinV6]
    exact weil_compact_smooth_mellin_vertical_integrable_all_v1 f c
  have hv :
      Integrable (fun v : ℝ => Real.exp (-δ * v))
        (volume.restrict (Ioi (0 : ℝ))) := by
    exact integrableOn_exp_mul_Ioi (a := -δ) (by linarith) 0
  have hmajor :
      Integrable
        (fun p : ℝ × ℝ =>
          ‖F p.1‖ * Real.exp (-δ * p.2))
        (volume.prod (volume.restrict (Ioi (0 : ℝ)))) :=
    hF.norm.mul_prod hv
  have hFmeas :
      AEStronglyMeasurable
        (fun p : ℝ × ℝ => F p.1)
        (volume.prod (volume.restrict (Ioi (0 : ℝ)))) :=
    hF.aestronglyMeasurable.comp_fst
  have hexp :
      Continuous (fun p : ℝ × ℝ =>
        Complex.exp
          (-((((c : ℂ) + (p.1 : ℂ) * I) - a) * (p.2 : ℂ)))) := by
    fun_prop
  have hmeas :
      AEStronglyMeasurable
        (WeilFixedLineLaplaceKernelV6 f c a)
        (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    exact hexp.aestronglyMeasurable.mul hFmeas
  refine hmajor.mono' hmeas
    (Filter.Eventually.of_forall fun p => ?_)
  unfold WeilFixedLineLaplaceKernelV6
  rw [norm_mul, weil_fixed_line_laplace_factor_norm_v6]
  dsimp [F, δ]
  rw [neg_mul]
  exact le_of_eq (mul_comm _ _)

/-- Fubini exchange for the fixed-line Laplace/Mellin kernel. -/
theorem weil_fixed_line_laplace_mellin_fubini_v6
    (f : WeilCompactSmoothGV1) (c : ℝ) (a : ℂ) (ha : a.re < c) :
    (∫ t : ℝ,
      ∫ v : ℝ in Ioi (0 : ℝ),
        WeilFixedLineLaplaceKernelV6 f c a (t, v)) =
      ∫ v : ℝ in Ioi (0 : ℝ),
        ∫ t : ℝ,
          WeilFixedLineLaplaceKernelV6 f c a (t, v) := by
  have hprod :=
    weil_fixed_line_laplace_mellin_product_integrable_v6 f c a ha
  simpa [Function.uncurry_def] using
    (integral_integral_swap
      (μ := volume) (ν := volume.restrict (Ioi (0 : ℝ)))
      (f := fun t v => WeilFixedLineLaplaceKernelV6 f c a (t, v))
      hprod)

/-- Evaluate the v-integral first: this is exactly the Cauchy kernel
F(c+it)/(c+it-a). -/
theorem weil_fixed_line_laplace_mellin_left_v6
    (f : WeilCompactSmoothGV1) (c : ℝ) (a : ℂ) (ha : a.re < c) :
    (∫ t : ℝ,
      ∫ v : ℝ in Ioi (0 : ℝ),
        WeilFixedLineLaplaceKernelV6 f c a (t, v)) =
      ∫ t : ℝ,
        (1 / (((c : ℂ) + (t : ℂ) * I) - a)) *
          WeilFixedLineMellinV6 f c t := by
  apply integral_congr_ae
  filter_upwards [] with t
  change
    (∫ v : ℝ in Ioi (0 : ℝ),
      Complex.exp
        (-((((c : ℂ) + (t : ℂ) * I) - a) * (v : ℂ))) *
        WeilFixedLineMellinV6 f c t) =
      (1 / (((c : ℂ) + (t : ℂ) * I) - a)) *
        WeilFixedLineMellinV6 f c t
  rw [integral_mul_const]
  rw [weil_fixed_line_laplace_kernel_integral_v6 c t a ha]

private theorem weil_exp_real_cpow_neg_line_v6
    (c t v : ℝ) :
    (((Real.exp v : ℝ) : ℂ) ^
      (-((c : ℂ) + (t : ℂ) * I))) =
      Complex.exp
        (-(((c : ℂ) + (t : ℂ) * I) * (v : ℂ))) := by
  have hx : (((Real.exp v : ℝ) : ℂ) ≠ 0) := by
    exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero v)
  rw [Complex.cpow_def_of_ne_zero hx]
  have hlog :
      Complex.log (((Real.exp v : ℝ) : ℂ)) = (v : ℂ) := by
    rw [← Complex.ofReal_log (Real.exp_pos v).le, Real.log_exp]
  rw [hlog]
  congr 1
  ring

/-- Mellin inversion specialized to x=exp(v), in the exact integrand shape
used by the Laplace kernel. -/
theorem weil_compact_smooth_mellin_inversion_exp_line_v6
    (f : WeilCompactSmoothGV1) (c v : ℝ) :
    ((1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ,
        Complex.exp
          (-(((c : ℂ) + (t : ℂ) * I) * (v : ℂ))) *
          WeilFixedLineMellinV6 f c t) =
      f.1 (Real.exp v) := by
  have h :=
    weil_compact_smooth_mellin_inversion_v1
      f c (x := Real.exp v) (Real.exp_pos v)
  rw [mellinInv] at h
  simp only [smul_eq_mul] at h
  simp_rw [weil_exp_real_cpow_neg_line_v6] at h
  simpa [WeilFixedLineMellinV6] using h

private theorem weil_fixed_line_laplace_factor_split_v6
    (c t v : ℝ) (a : ℂ) :
    Complex.exp
      (-((((c : ℂ) + (t : ℂ) * I) - a) * (v : ℂ))) =
      Complex.exp (a * (v : ℂ)) *
        Complex.exp
          (-(((c : ℂ) + (t : ℂ) * I) * (v : ℂ))) := by
  rw [← Complex.exp_add]
  congr 1
  ring

/-- Evaluate the t-integral after Fubini using the already verified Mellin
inversion theorem. -/
theorem weil_fixed_line_laplace_mellin_right_v6
    (f : WeilCompactSmoothGV1) (c : ℝ) (a : ℂ) :
    ((1 / (2 * Real.pi) : ℂ) *
      (∫ v : ℝ in Ioi (0 : ℝ),
        ∫ t : ℝ,
          WeilFixedLineLaplaceKernelV6 f c a (t, v))) =
      ∫ v : ℝ in Ioi (0 : ℝ),
        Complex.exp (a * (v : ℂ)) * f.1 (Real.exp v) := by
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  change
    (1 / (2 * Real.pi) : ℂ) *
        (∫ t : ℝ, WeilFixedLineLaplaceKernelV6 f c a (t, v)) =
      Complex.exp (a * (v : ℂ)) * f.1 (Real.exp v)
  have hinter :
      (∫ t : ℝ,
        WeilFixedLineLaplaceKernelV6 f c a (t, v)) =
        Complex.exp (a * (v : ℂ)) *
          ∫ t : ℝ,
            Complex.exp
              (-(((c : ℂ) + (t : ℂ) * I) * (v : ℂ))) *
              WeilFixedLineMellinV6 f c t := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    unfold WeilFixedLineLaplaceKernelV6
    rw [weil_fixed_line_laplace_factor_split_v6]
    ring
  change
    (1 / (2 * Real.pi) : ℂ) *
        (∫ t : ℝ, WeilFixedLineLaplaceKernelV6 f c a (t, v)) =
      Complex.exp (a * (v : ℂ)) * f.1 (Real.exp v)
  rw [hinter]
  have hinv :=
    weil_compact_smooth_mellin_inversion_exp_line_v6 f c v
  calc
    (1 / (2 * Real.pi) : ℂ) *
        (Complex.exp (a * (v : ℂ)) *
          ∫ t : ℝ,
            Complex.exp
              (-(((c : ℂ) + (t : ℂ) * I) * (v : ℂ))) *
              WeilFixedLineMellinV6 f c t)
        =
      Complex.exp (a * (v : ℂ)) *
        ((1 / (2 * Real.pi) : ℂ) *
          ∫ t : ℝ,
            Complex.exp
              (-(((c : ℂ) + (t : ℂ) * I) * (v : ℂ))) *
              WeilFixedLineMellinV6 f c t) := by ring
    _ = Complex.exp (a * (v : ℂ)) * f.1 (Real.exp v) := by
      rw [hinv]

/-- The machine-checked KI identity in logarithmic coordinates. -/
theorem weil_fixed_line_kernel_integral_log_v6
    (f : WeilCompactSmoothGV1) (c : ℝ) (a : ℂ) (ha : a.re < c) :
    ((1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ,
        (1 / (((c : ℂ) + (t : ℂ) * I) - a)) *
          WeilFixedLineMellinV6 f c t) =
      ∫ v : ℝ in Ioi (0 : ℝ),
        Complex.exp (a * (v : ℂ)) * f.1 (Real.exp v) := by
  calc
    ((1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ,
        (1 / (((c : ℂ) + (t : ℂ) * I) - a)) *
          WeilFixedLineMellinV6 f c t)
        =
      (1 / (2 * Real.pi) : ℂ) *
        (∫ t : ℝ,
          ∫ v : ℝ in Ioi (0 : ℝ),
            WeilFixedLineLaplaceKernelV6 f c a (t, v)) := by
              rw [weil_fixed_line_laplace_mellin_left_v6 f c a ha]
    _ =
      (1 / (2 * Real.pi) : ℂ) *
        (∫ v : ℝ in Ioi (0 : ℝ),
          ∫ t : ℝ,
            WeilFixedLineLaplaceKernelV6 f c a (t, v)) := by
              rw [weil_fixed_line_laplace_mellin_fubini_v6 f c a ha]
    _ =
      ∫ v : ℝ in Ioi (0 : ℝ),
        Complex.exp (a * (v : ℂ)) * f.1 (Real.exp v) :=
      weil_fixed_line_laplace_mellin_right_v6 f c a

end

#print axioms weil_fixed_line_laplace_kernel_integral_v6
#print axioms weil_fixed_line_laplace_mellin_product_integrable_v6
#print axioms weil_fixed_line_laplace_mellin_fubini_v6
#print axioms weil_compact_smooth_mellin_inversion_exp_line_v6
#print axioms weil_fixed_line_kernel_integral_log_v6
