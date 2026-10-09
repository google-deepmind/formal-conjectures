import ZeroShellQuadraticBoundV1

/-!
AEGIS Ω — analytic shell synthesis v1.

This module is a pure synthesis layer over the already verified finite
height-shell and quadratic-shell infrastructure. It introduces two explicit
analytic interfaces:

* a linear bound on total analytic-order multiplicity mass in each shell;
* a cubic pointwise Mellin-decay bound on each shell.

From those two supplied inputs it proves the existing
`HasQuadraticShellMassBoundV1` certificate. The module does not prove either
analytic input, does not assume that nontrivial zeros lie on the critical line,
and does not prove an explicit formula, the Weil criterion, or RH.

ZERO_SHELL_ANALYTIC_SYNTHESIS_ONLY
ACTUAL_LINEAR_SHELL_MULTIPLICITY_BOUND_OPEN
ACTUAL_CUBIC_SHELL_MELLIN_DECAY_OPEN
ACTUAL_QUADRATIC_SHELL_BOUND_OPEN
ZERO_COUNTING_BOUND_OPEN
MELLIN_DECAY_ESTIMATE_OPEN
WEIL_CLASS_SHELL_MASS_SUMMABILITY_OPEN
CONDITIONAL_SYMMETRIC_CONVERGENCE_OPEN
EXPLICIT_FORMULA_OPEN
CRITICAL_LINE_RE_HALF_OPEN
RH_EQUIVALENCE_OPEN
-/

open Set Filter Topology
open Complex

noncomputable section

/-- Total analytic-order multiplicity mass in the `n`-th verified height
shell. The shell itself is the existing `ZeroHeightShellSetV1 n`; no parallel
zero carrier is introduced here. -/
def ZeroHeightShellMultiplicityMassV1 (n : ℕ) : ℝ :=
  ∑' rho : ZeroHeightShellSetV1 n,
    (analyticOrderNatAt riemannZeta rho.1.1 : ℝ)

/-- Weak zero-counting interface sufficient for the synthesis layer. A sharper
Riemann-von Mangoldt shell estimate may later discharge this premise, but this
module consumes only the linear majorant actually needed downstream. -/
def HasLinearShellMultiplicityBoundV1 : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧
    ∀ n : ℕ,
      ZeroHeightShellMultiplicityMassV1 n ≤
        A * ((n + 1 : ℕ) : ℝ)

/-- Shell-local cubic Mellin-decay interface. A later Mellin/Fourier analysis
must construct this certificate uniformly for the intended test-function
class. -/
def HasCubicShellMellinDecayV1 (f : ℝ → ℂ) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧
    ∀ (n : ℕ) (rho : ZeroHeightShellSetV1 n),
      ‖mellin f rho.1.1‖ ≤
        B / (((n + 1 : ℕ) : ℝ) ^ 3)

/-- Linear multiplicity mass plus cubic pointwise Mellin decay implies the
quadratic shell certificate already consumed by `ZeroShellQuadraticBoundV1`.
This theorem is synthesis only: the two analytic premises remain independent
obligations. -/
theorem shell_count_and_mellin_decay_imply_quadratic_bound_v1
    {f : ℝ → ℂ}
    (hcount : HasLinearShellMultiplicityBoundV1)
    (hdecay : HasCubicShellMellinDecayV1 f) :
    HasQuadraticShellMassBoundV1 f := by
  classical
  rcases hcount with ⟨A, hA, hcount_bound⟩
  rcases hdecay with ⟨B, hB, hdecay_bound⟩
  refine ⟨A * B, mul_nonneg hA hB, ?_⟩
  intro n

  letI : Fintype (ZeroHeightShellSetV1 n) :=
    (zero_height_shell_finite_v1 n).fintype

  let t : ℝ := ((n + 1 : ℕ) : ℝ)
  have ht : 0 < t := by
    dsimp [t]
    positivity

  have hfactor : 0 ≤ B / t ^ 3 := by
    exact div_nonneg hB (by positivity)

  have hcount_n :
      (∑ rho : ZeroHeightShellSetV1 n,
        (analyticOrderNatAt riemannZeta rho.1.1 : ℝ)) ≤
      A * t := by
    simpa [ZeroHeightShellMultiplicityMassV1, tsum_fintype, t]
      using hcount_bound n

  have hterm :
      ∀ rho : ZeroHeightShellSetV1 n,
        ‖WeilZeroIndexSummandV1 f rho.1‖ ≤
          (analyticOrderNatAt riemannZeta rho.1.1 : ℝ) *
            (B / t ^ 3) := by
    intro rho
    have hm :
        0 ≤ (analyticOrderNatAt riemannZeta rho.1.1 : ℝ) := by
      positivity
    have hmul :=
      mul_le_mul_of_nonneg_left (hdecay_bound n rho) hm
    simpa [WeilZeroIndexSummandV1, norm_mul, t] using hmul

  change
    ZeroHeightShellMassV1 f n ≤
      QuadraticShellReferenceV1 (A * B) n

  calc
    ZeroHeightShellMassV1 f n =
        ∑ rho : ZeroHeightShellSetV1 n,
          ‖WeilZeroIndexSummandV1 f rho.1‖ := by
      simp [ZeroHeightShellMassV1, tsum_fintype]
    _ ≤
        ∑ rho : ZeroHeightShellSetV1 n,
          (analyticOrderNatAt riemannZeta rho.1.1 : ℝ) *
            (B / t ^ 3) := by
      exact Finset.sum_le_sum fun rho _ => hterm rho
    _ =
        (∑ rho : ZeroHeightShellSetV1 n,
          (analyticOrderNatAt riemannZeta rho.1.1 : ℝ)) *
            (B / t ^ 3) := by
      simpa only [Finset.sum_mul]
    _ ≤ (A * t) * (B / t ^ 3) := by
      exact mul_le_mul_of_nonneg_right hcount_n hfactor
    _ = QuadraticShellReferenceV1 (A * B) n := by
      unfold QuadraticShellReferenceV1
      change
        (A * t) * (B / t ^ 3) =
          (A * B) * (1 / t ^ 2)
      field_simp [ne_of_gt ht]

#check ZeroHeightShellMultiplicityMassV1
#check HasLinearShellMultiplicityBoundV1
#check HasCubicShellMellinDecayV1
#check shell_count_and_mellin_decay_imply_quadratic_bound_v1
#print axioms shell_count_and_mellin_decay_imply_quadratic_bound_v1
