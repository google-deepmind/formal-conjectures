import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.ZetaZeros

/-!
AEGIS Ω — finite nontrivial-zeta-zero truncation v1.

This lane defines only compact radial truncations and their finite weighted sums.
It does not assert existence of the global radial limit, equivalence with a
height-ordered convention, an explicit-formula identity, or RH.

FINITE_ZERO_TRUNCATION_ONLY
GLOBAL_ZERO_LIMIT_PROOF_OPEN
HEIGHT_TRUNCATION_EQUIVALENCE_OPEN
EXPLICIT_FORMULA_THEOREM_OPEN
RH_EQUIVALENCE_OPEN
-/

open Set Filter Topology
open Complex
open scoped BigOperators

noncomputable section

/-- The set of nontrivial Riemann-zeta zeros using the same exclusions as the
    Mathlib Riemann-hypothesis target. -/
def RiemannNontrivialZeroSetV1 : Set ℂ :=
  { rho | rho ∈ riemannZetaZeros ∧
      (¬ ∃ n : ℕ, rho = -2 * (n + 1)) ∧
      rho ≠ 1 }

/-- Compact radial truncation region. -/
def ZeroRadialRegionV1 (R : ℝ) : Set ℂ :=
  Metric.closedBall 0 R

/-- Nontrivial zeta zeros lying in the radial truncation region. -/
def ZeroRadialSetV1 (R : ℝ) : Set ℂ :=
  ZeroRadialRegionV1 R ∩ RiemannNontrivialZeroSetV1

/-- Every radial truncation contains only finitely many nontrivial zeta zeros.

The proof is a subset of Mathlib's pinned compact-zero finiteness theorem for
`riemannZetaZeros`; no global ordering or convergence claim is used. -/
theorem zero_radial_set_finite_v1 (R : ℝ) :
    (ZeroRadialSetV1 R).Finite := by
  have hAll :
      (Metric.closedBall (0 : ℂ) R ∩ riemannZetaZeros).Finite :=
    (isCompact_closedBall (0 : ℂ) R).inter_riemannZetaZeros_finite
  refine hAll.subset ?_
  intro z hz
  change z ∈ Metric.closedBall (0 : ℂ) R ∧ z ∈ RiemannNontrivialZeroSetV1 at hz
  rcases hz with ⟨hzBall, hzNontrivial⟩
  change
    z ∈ riemannZetaZeros ∧
      (¬ ∃ n : ℕ, z = -2 * (n + 1)) ∧
      z ≠ 1 at hzNontrivial
  exact ⟨hzBall, hzNontrivial.1⟩

/-- Canonical finite carrier for one radial truncation. -/
def ZeroRadialFinsetV1 (R : ℝ) : Finset ℂ :=
  (zero_radial_set_finite_v1 R).toFinset

/-- Membership in the finite carrier is exactly membership in the truncation set. -/
theorem mem_zero_radial_finset_v1 (R : ℝ) (rho : ℂ) :
    rho ∈ ZeroRadialFinsetV1 R ↔ rho ∈ ZeroRadialSetV1 R := by
  classical
  simp [ZeroRadialFinsetV1]

/-- Finite multiplicity-weighted Mellin zero-side sum at radius `R`.

Because the carrier is a `Finset`, this object requires no infinite-summation
convention and makes no convergence assertion. -/
def WeilZeroRadialTruncatedSumV1 (f : ℝ → ℂ) (R : ℝ) : ℂ :=
  (ZeroRadialFinsetV1 R).sum fun rho =>
    (analyticOrderNatAt riemannZeta rho : ℂ) * mellin f rho

/-- The selected radial-limit convention, stated only as a proposition.

A later lane must prove this proposition for an appropriate test-function class
and then relate it to the desired explicit formula. -/
def WeilZeroRadialLimitConventionV1 (f : ℝ → ℂ) (L : ℂ) : Prop :=
  Tendsto (fun R : ℝ => WeilZeroRadialTruncatedSumV1 f R) atTop (𝓝 L)

#check RiemannNontrivialZeroSetV1
#check ZeroRadialRegionV1
#check ZeroRadialSetV1
#check zero_radial_set_finite_v1
#check ZeroRadialFinsetV1
#check mem_zero_radial_finset_v1
#check WeilZeroRadialTruncatedSumV1
#check WeilZeroRadialLimitConventionV1

#print axioms zero_radial_set_finite_v1
#print axioms mem_zero_radial_finset_v1
