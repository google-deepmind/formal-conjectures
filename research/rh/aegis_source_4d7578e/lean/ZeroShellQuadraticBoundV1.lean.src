import ZeroHeightShellMassV1
import Mathlib.Analysis.PSeries

/-!
AEGIS Ω — quadratic height-shell mass bound reduction v1.

This lane proves only a sufficient quantitative reduction. If the already
verified shell norm-masses admit a uniform bound of the form

  shellMass(f,n) ≤ C * 1 / (n+1)^2

for some nonnegative constant `C`, then the shell-mass series is summable.
Consequently the previously verified shell bridge yields unconditional
summability of the zero-side Mellin summand and an actual symmetric-height
limit witness.

The lane does not prove that such a quadratic bound holds for any Weil/Bombieri
test class. The actual Mellin-decay estimate and quantitative zero-counting
input needed to establish such a bound remain separate open obligations.

QUADRATIC_SHELL_BOUND_SUFFICIENT_ONLY
ACTUAL_QUADRATIC_SHELL_BOUND_OPEN
MELLIN_DECAY_ESTIMATE_OPEN
ZERO_COUNTING_BOUND_OPEN
WEIL_CLASS_SHELL_MASS_SUMMABILITY_OPEN
CONDITIONAL_SYMMETRIC_CONVERGENCE_OPEN
EXPLICIT_FORMULA_OPEN
CRITICAL_LINE_RE_HALF_OPEN
RH_EQUIVALENCE_OPEN
-/

open Set Filter Topology

noncomputable section

/-- Quadratic comparison sequence used only as a sufficient shell-mass
majorant. The shift by one avoids the singular term at `n = 0`. -/
def QuadraticShellReferenceV1 (C : ℝ) (n : ℕ) : ℝ :=
  C * (1 / (((n + 1 : ℕ) : ℝ) ^ 2))

/-- Certificate that every finite shell norm-mass is bounded by one fixed
quadratic p-series majorant. This is a definition, not an existence theorem. -/
def HasQuadraticShellMassBoundV1 (f : ℝ → ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ n : ℕ, ZeroHeightShellMassV1 f n ≤ QuadraticShellReferenceV1 C n

private theorem zero_height_shell_mass_nonneg_v1 (f : ℝ → ℂ) (n : ℕ) :
    0 ≤ ZeroHeightShellMassV1 f n := by
  unfold ZeroHeightShellMassV1
  exact tsum_nonneg fun _ => norm_nonneg _

private theorem quadratic_shell_reference_summable_v1 (C : ℝ) :
    Summable (QuadraticShellReferenceV1 C) := by
  unfold QuadraticShellReferenceV1
  apply Summable.mul_left C
  have hp0 : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  have hshift :=
    (summable_nat_add_iff (f := fun n : ℕ => 1 / ((n : ℝ) ^ 2)) 1).mpr hp0
  simpa [Nat.cast_add, Nat.cast_one] using hshift

/-- A supplied quadratic shell-mass bound makes the shell-mass sequence
summable by direct comparison with the shifted p-series of exponent two. -/
theorem quadratic_shell_bound_implies_summable_v1
    {f : ℝ → ℂ} (h : HasQuadraticShellMassBoundV1 f) :
    Summable (ZeroHeightShellMassV1 f) := by
  rcases h with ⟨C, _hC, hbound⟩
  exact Summable.of_nonneg_of_le
    (fun n => zero_height_shell_mass_nonneg_v1 f n)
    hbound
    (quadratic_shell_reference_summable_v1 C)

/-- Under the supplied quadratic shell certificate, the complex zero-side
summand is unconditionally summable. -/
theorem quadratic_shell_bound_implies_zero_summable_v1
    {f : ℝ → ℂ} (h : HasQuadraticShellMassBoundV1 f) :
    Summable (WeilZeroIndexSummandV1 f) := by
  exact zero_summable_of_shell_mass_v1
    (quadratic_shell_bound_implies_summable_v1 h)

/-- Under the supplied quadratic shell certificate, the already verified
symmetric-height limit contract has an actual witness. This theorem does not
construct the certificate. -/
theorem quadratic_shell_bound_implies_height_limit_v1
    {f : ℝ → ℂ} (h : HasQuadraticShellMassBoundV1 f) :
    WeilZeroHeightLimitExistsV1 f := by
  exact shell_mass_implies_height_limit_exists_v1
    (quadratic_shell_bound_implies_summable_v1 h)

#check QuadraticShellReferenceV1
#check HasQuadraticShellMassBoundV1
#check quadratic_shell_bound_implies_summable_v1
#check quadratic_shell_bound_implies_zero_summable_v1
#check quadratic_shell_bound_implies_height_limit_v1
#print axioms quadratic_shell_bound_implies_summable_v1
#print axioms quadratic_shell_bound_implies_zero_summable_v1
#print axioms quadratic_shell_bound_implies_height_limit_v1
