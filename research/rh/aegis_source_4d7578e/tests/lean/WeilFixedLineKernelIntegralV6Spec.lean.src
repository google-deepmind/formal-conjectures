import WeilFixedLineKernelIntegralV6

open Set Filter Topology Complex MeasureTheory
open scoped BigOperators

set_option autoImplicit false

noncomputable section

example (f : WeilCompactSmoothGV1) (c : ℝ) (a : ℂ) (ha : a.re < c) :
    ((1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ,
        (1 / (((c : ℂ) + (t : ℂ) * I) - a)) *
          WeilFixedLineMellinV6 f c t) =
      ∫ v : ℝ in Ioi (0 : ℝ),
        Complex.exp (a * (v : ℂ)) * f.1 (Real.exp v) :=
  weil_fixed_line_kernel_integral_log_v6 f c a ha
