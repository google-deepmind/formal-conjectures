import ZeroHeightSummabilityBridgeV1
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
AEGIS Ω — summable norm-majorant bridge for the nontrivial zeta-zero side v1.

This lane proves a standard direct-comparison reduction only. If one supplies a
real-valued summable majorant that pointwise dominates the norm of the already
verified multiplicity-weighted Mellin summand, then the zero-side summand is
unconditionally summable. The verified `HasSum -> height limit` bridge then
produces an actual height-limit witness, and that witness is uniquely the
unordered `tsum` under this strong hypothesis.

This lane does not construct such a majorant for the Weil/Bombieri test class.
It does not assert that unconditional summability is the weakest classical
summation convention needed by the explicit formula.

ZERO_MAJORANT_SUFFICIENT_ONLY
ACTUAL_MAJORANT_CONSTRUCTION_OPEN
WEIL_CLASS_MAJORANT_OPEN
CONDITIONAL_SYMMETRIC_CONVERGENCE_OPEN
EXPLICIT_FORMULA_OPEN
CRITICAL_LINE_RE_HALF_OPEN
RH_EQUIVALENCE_OPEN
-/

open Filter Topology

noncomputable section

/-- A concrete sufficient certificate for unconditional summability of the
multiplicity-weighted nontrivial-zero Mellin summand. -/
def HasSummableZeroMajorantV1 (f : ℝ → ℂ) : Prop :=
  ∃ g : RiemannNontrivialZeroIndexV2 → ℝ,
    Summable g ∧
      ∀ rho : RiemannNontrivialZeroIndexV2,
        ‖WeilZeroIndexSummandV1 f rho‖ ≤ g rho

/-- Direct comparison: a supplied summable norm-majorant makes the zero-side
summand unconditionally summable. -/
theorem zero_summable_of_majorant_v1
    {f : ℝ → ℂ} (h : HasSummableZeroMajorantV1 f) :
    Summable (WeilZeroIndexSummandV1 f) := by
  rcases h with ⟨g, hg, hbound⟩
  exact Summable.of_norm_bounded hg hbound

/-- Under the strong majorant certificate, the previously verified symmetric
height-limit contract has an actual witness. This does not construct the
certificate itself. -/
theorem majorant_implies_height_limit_exists_v1
    {f : ℝ → ℂ} (h : HasSummableZeroMajorantV1 f) :
    WeilZeroHeightLimitExistsV1 f := by
  have hsum : Summable (WeilZeroIndexSummandV1 f) :=
    zero_summable_of_majorant_v1 h
  refine ⟨∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1 f rho, ?_⟩
  exact hasSum_implies_height_limit_v1 hsum.hasSum

/-- Any symmetric height-limit witness under the same majorant certificate is
the unordered `tsum`. The conclusion is conditional on the strong majorant. -/
theorem majorant_height_limit_eq_tsum_v1
    {f : ℝ → ℂ} {L : ℂ}
    (h : HasSummableZeroMajorantV1 f)
    (hL : HasWeilZeroHeightLimitV1 f L) :
    L = ∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1 f rho := by
  have hsum : Summable (WeilZeroIndexSummandV1 f) :=
    zero_summable_of_majorant_v1 h
  have hTsum :
      HasWeilZeroHeightLimitV1 f
        (∑' rho : RiemannNontrivialZeroIndexV2,
          WeilZeroIndexSummandV1 f rho) :=
    hasSum_implies_height_limit_v1 hsum.hasSum
  exact weil_zero_height_limit_unique_v1 hL hTsum

#check HasSummableZeroMajorantV1
#check zero_summable_of_majorant_v1
#check majorant_implies_height_limit_exists_v1
#check majorant_height_limit_eq_tsum_v1
#print axioms zero_summable_of_majorant_v1
#print axioms majorant_implies_height_limit_exists_v1
#print axioms majorant_height_limit_eq_tsum_v1
