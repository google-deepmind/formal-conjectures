import WeilFixedLineXSpaceTailV7

open Set Filter Topology Complex MeasureTheory
open scoped BigOperators

set_option autoImplicit false

noncomputable section

example (f : WeilCompactSmoothGV1) (a : ℂ) :
    (∫ v : ℝ in Ioi (0 : ℝ),
      Complex.exp (a * (v : ℂ)) * f.1 (Real.exp v)) =
      ∫ x : ℝ in Ioi (1 : ℝ),
        ((x : ℂ) ^ (a - 1)) * f.1 x :=
  weil_fixed_line_log_tail_eq_x_tail_v7 f a

example
    (f : WeilCompactSmoothGV1) (c : ℝ) (a : ℂ) (ha : a.re < c) :
    ((1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ,
        (1 / (((c : ℂ) + (t : ℂ) * I) - a)) *
          WeilFixedLineMellinV6 f c t) =
      ∫ x : ℝ in Ioi (1 : ℝ),
        ((x : ℂ) ^ (a - 1)) * f.1 x :=
  weil_fixed_line_kernel_integral_x_tail_v7 f c a ha
