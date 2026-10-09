import WeilFixedLineKernelIntegralV6
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
AEGIS Ω — fixed-line x-space Mellin tail rewrite v7.

This child of the GREEN V6 kernel-integral lane performs exactly the remaining
change of variables x = exp(v) in the KI identity:

  ∫_{v>0} exp(a v) f(exp v) dv
    = ∫_{x>1} x^(a-1) f(x) dx.

It then composes that equality with the V6 fixed-line Cauchy/Mellin identity.
No paired-zero evaluation, zero-sum reindexing, gamma/digamma normalization,
whole explicit formula, arithmetic sign, global Weil positivity, or RH
conclusion is asserted here.
-/

open Set Filter Topology Complex MeasureTheory
open scoped BigOperators

set_option autoImplicit false

noncomputable section

private theorem weil_exp_real_cpow_sub_one_v7
    (a : ℂ) (v : ℝ) :
    (((Real.exp v : ℝ) : ℂ) *
      (((Real.exp v : ℝ) : ℂ) ^ (a - 1))) =
      Complex.exp (a * (v : ℂ)) := by
  have hx : (((Real.exp v : ℝ) : ℂ) ≠ 0) := by
    exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero v)
  rw [Complex.cpow_def_of_ne_zero hx]
  have hlog :
      Complex.log (((Real.exp v : ℝ) : ℂ)) = (v : ℂ) := by
    rw [← Complex.ofReal_log (Real.exp_pos v).le, Real.log_exp]
  rw [hlog, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  ring

/-- Exact x = exp(v) rewrite of the logarithmic KI tail. -/
theorem weil_fixed_line_log_tail_eq_x_tail_v7
    (f : WeilCompactSmoothGV1) (a : ℂ) :
    (∫ v : ℝ in Ioi (0 : ℝ),
      Complex.exp (a * (v : ℂ)) * f.1 (Real.exp v)) =
      ∫ x : ℝ in Ioi (1 : ℝ),
        ((x : ℂ) ^ (a - 1)) * f.1 x := by
  have h :=
    integral_comp_exp_Ioi
      (fun x : ℝ => ((x : ℂ) ^ (a - 1)) * f.1 x) 0
  calc
    (∫ v : ℝ in Ioi (0 : ℝ),
      Complex.exp (a * (v : ℂ)) * f.1 (Real.exp v))
        =
      ∫ v : ℝ in Ioi (0 : ℝ),
        Real.exp v •
          ((((Real.exp v : ℝ) : ℂ) ^ (a - 1)) *
            f.1 (Real.exp v)) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro v hv
          change
            Complex.exp (a * (v : ℂ)) * f.1 (Real.exp v) =
              ((Real.exp v : ℝ) : ℂ) *
                ((((Real.exp v : ℝ) : ℂ) ^ (a - 1)) *
                  f.1 (Real.exp v))
          rw [← mul_assoc, weil_exp_real_cpow_sub_one_v7]
    _ =
      ∫ x : ℝ in Ioi (1 : ℝ),
        ((x : ℂ) ^ (a - 1)) * f.1 x := by
          simpa [Complex.real_smul] using h

/-- V6 KI identity rewritten on the actual x>1 Mellin tail. -/
theorem weil_fixed_line_kernel_integral_x_tail_v7
    (f : WeilCompactSmoothGV1) (c : ℝ) (a : ℂ) (ha : a.re < c) :
    ((1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ,
        (1 / (((c : ℂ) + (t : ℂ) * I) - a)) *
          WeilFixedLineMellinV6 f c t) =
      ∫ x : ℝ in Ioi (1 : ℝ),
        ((x : ℂ) ^ (a - 1)) * f.1 x := by
  rw [weil_fixed_line_kernel_integral_log_v6 f c a ha]
  exact weil_fixed_line_log_tail_eq_x_tail_v7 f a

end

#print axioms weil_fixed_line_log_tail_eq_x_tail_v7
#print axioms weil_fixed_line_kernel_integral_x_tail_v7
