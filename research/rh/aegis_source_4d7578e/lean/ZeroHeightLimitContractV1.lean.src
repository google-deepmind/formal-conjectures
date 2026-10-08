import ZeroHeightFiniteSumV1

/-!
AEGIS Ω — symmetric height-limit contract for multiplicity-weighted zeta-zero sums v1.

This lane formalizes only what it means for the already verified finite,
multiplicity-weighted height truncations to converge as the height parameter
`T : ℝ` tends to `+∞`. It also proves that any such limit is unique.

It does not prove that a limit exists, does not replace this height convention
with an unordered infinite sum, and does not prove an explicit formula, the
critical-line statement, or RH.

HEIGHT_LIMIT_CONTRACT_ONLY
HEIGHT_LIMIT_EXISTENCE_OPEN
ZERO_SUM_CONVERGENCE_OPEN
EXPLICIT_FORMULA_OPEN
CRITICAL_LINE_RE_HALF_OPEN
RH_EQUIVALENCE_OPEN
-/

open Filter Topology

/-- `L` is the symmetric-height limit of the finite multiplicity-weighted
Mellin sums when `T → +∞`. -/
def HasWeilZeroHeightLimitV1 (f : ℝ → ℂ) (L : ℂ) : Prop :=
  Tendsto (fun T : ℝ => WeilZeroHeightTruncatedSumV1 f T) atTop (𝓝 L)

/-- Merely the proposition that a height-limit witness exists. This definition
asserts no theorem of existence. -/
def WeilZeroHeightLimitExistsV1 (f : ℝ → ℂ) : Prop :=
  ∃ L : ℂ, HasWeilZeroHeightLimitV1 f L

/-- If the height-limit contract holds for two candidate values, they are equal.
This proves uniqueness only, not existence. -/
theorem weil_zero_height_limit_unique_v1
    {f : ℝ → ℂ} {L M : ℂ}
    (hL : HasWeilZeroHeightLimitV1 f L)
    (hM : HasWeilZeroHeightLimitV1 f M) :
    L = M := by
  exact tendsto_nhds_unique hL hM

#check HasWeilZeroHeightLimitV1
#check WeilZeroHeightLimitExistsV1
#check weil_zero_height_limit_unique_v1
#print axioms weil_zero_height_limit_unique_v1
