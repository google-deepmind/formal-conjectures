import WeilFiniteSourceCalculusV1
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Tactic

/-!
AEGIS Ω — true Archimedean sine-source kernel v1.

This module starts the analytic identification between the actual truncated
Archimedean source and the rational Cauchy core already isolated in
`WeilFiniteSourceCalculusV1`.

It proves differentiation of the true parameter-dependent source integral with
respect to the Galerkin coordinate. The integer-node closed forms are the next
bounded obligations. No Cauchy--Stieltjes integration, PSD import, operator
order, global Weil positivity, formula-to-Weil identity, or RH claim is made.
-/

open scoped BigOperators
open intervalIntegral

set_option autoImplicit false

noncomputable section

/-- `rho = 2π/L`, the Galerkin frequency scale. -/
def WeilArchRhoV1 (L : ℝ) : ℝ :=
  2 * Real.pi / L

/-- True truncated Archimedean sine source before the outer `h₊(T)` weight. -/
def WeilArchSineKernelV1 (L T x : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..L,
    Real.sin (2 * Real.pi * x * (1 - y / L)) * Real.cos (T * y)

/-- Pointwise x-derivative integrated over the true Archimedean source. -/
def WeilArchSineKernelDxV1 (L T x : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..L,
    (2 * Real.pi * (1 - y / L) *
      Real.cos (2 * Real.pi * x * (1 - y / L))) *
      Real.cos (T * y)

/-- Differentiation under the finite interval integral for the actual source.
This is the load-bearing diagonal bridge: the diagonal Galerkin entry is the
x-derivative of the true source, not of a node-only surrogate. -/
theorem weil_arch_sine_kernel_hasDerivAt_v1
    (L T x : ℝ) :
    HasDerivAt (WeilArchSineKernelV1 L T)
      (WeilArchSineKernelDxV1 L T x) x := by
  unfold WeilArchSineKernelV1 WeilArchSineKernelDxV1
  let F : ℝ → ℝ → ℝ := fun z y =>
    Real.sin (2 * Real.pi * z * (1 - y / L)) * Real.cos (T * y)
  let F' : ℝ → ℝ → ℝ := fun z y =>
    (2 * Real.pi * (1 - y / L) *
      Real.cos (2 * Real.pi * z * (1 - y / L))) * Real.cos (T * y)
  let bound : ℝ → ℝ := fun y => |2 * Real.pi * (1 - y / L)|
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := bound) (s := Set.univ) (x₀ := x)
    Filter.univ_mem ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards with z
    dsimp [F]
    fun_prop
  · dsimp [F]
    exact (by fun_prop : Continuous (fun y : ℝ =>
      Real.sin (2 * Real.pi * x * (1 - y / L)) * Real.cos (T * y))).intervalIntegrable 0 L
  · dsimp [F']
    fun_prop
  · filter_upwards with y hy z hz
    dsimp [F', bound]
    change
      ‖(2 * Real.pi * (1 - y / L) *
          Real.cos (2 * Real.pi * z * (1 - y / L))) * Real.cos (T * y)‖ ≤
        ‖2 * Real.pi * (1 - y / L)‖
    calc
      ‖(2 * Real.pi * (1 - y / L) *
          Real.cos (2 * Real.pi * z * (1 - y / L))) * Real.cos (T * y)‖ =
          ‖2 * Real.pi * (1 - y / L)‖ *
            ‖Real.cos (2 * Real.pi * z * (1 - y / L))‖ * ‖Real.cos (T * y)‖ := by
              rw [norm_mul, norm_mul]
      _ ≤ ‖2 * Real.pi * (1 - y / L)‖ * 1 * 1 := by
        gcongr
        · simpa [Real.norm_eq_abs] using Real.abs_cos_le_one
            (2 * Real.pi * z * (1 - y / L))
        · simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (T * y)
      _ = ‖2 * Real.pi * (1 - y / L)‖ := by ring
  · dsimp [bound]
    exact (by fun_prop : Continuous (fun y : ℝ =>
      |2 * Real.pi * (1 - y / L)|)).intervalIntegrable 0 L
  · filter_upwards with y hy z hz
    dsimp [F, F']
    have harg : HasDerivAt
        (fun w : ℝ => 2 * Real.pi * w * (1 - y / L))
        (2 * Real.pi * (1 - y / L)) z := by
      simpa [mul_assoc] using
        (((hasDerivAt_id z).const_mul (2 * Real.pi)).mul_const (1 - y / L))
    have hsin := (Real.hasDerivAt_sin
      (2 * Real.pi * z * (1 - y / L))).comp z harg
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      hsin.mul_const (Real.cos (T * y))

#print axioms weil_arch_sine_kernel_hasDerivAt_v1
