import ZeroMajorantSummabilityV1
import ZeroCriticalStripV1
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.Order.Floor.Semiring

/-!
AEGIS Ω — finite height-shell mass reduction for the nontrivial zeta-zero side v1.

Each nontrivial zero is assigned the canonical shell index `ceil |Im rho|`.
Using the already verified critical-strip localization and Mathlib compact-zero
finiteness, every shell is finite. Mathlib's nonnegative partition theorem then
reduces global norm-summability of the multiplicity-weighted Mellin zero
summand exactly to summability of the sequence of finite shell norm-masses.

This lane does not prove any decay estimate for those shell masses and does not
prove that their series is summable for the Weil/Bombieri test class.

FINITE_HEIGHT_SHELL_REDUCTION_ONLY
SHELL_MASS_DECAY_BOUND_OPEN
WEIL_CLASS_SHELL_MASS_SUMMABILITY_OPEN
CONDITIONAL_SYMMETRIC_CONVERGENCE_OPEN
EXPLICIT_FORMULA_OPEN
CRITICAL_LINE_RE_HALF_OPEN
RH_EQUIVALENCE_OPEN
-/

open Set Filter Topology
open Complex

noncomputable section

/-- Canonical natural-number shell index of a nontrivial zeta zero. -/
def ZeroHeightShellIndexV1 (rho : RiemannNontrivialZeroIndexV2) : ℕ :=
  Nat.ceil |rho.1.im|

/-- The `n`-th shell consists of nontrivial zeros whose canonical ceiling
height is exactly `n`. -/
def ZeroHeightShellSetV1 (n : ℕ) : Set RiemannNontrivialZeroIndexV2 :=
  {rho | ZeroHeightShellIndexV1 rho = n}

/-- Every canonical height shell is finite. The proof places a shell in the
compact disk of radius `n + 1`, using `0 < Re rho < 1` for nontrivial zeros. -/
theorem zero_height_shell_finite_v1 (n : ℕ) :
    (ZeroHeightShellSetV1 n).Finite := by
  rw [← Set.finite_coe_iff]
  let K : Set ℂ := Metric.closedBall (0 : ℂ) ((n : ℝ) + 1) ∩ riemannZetaZeros
  have hK : K.Finite :=
    IsCompact.inter_riemannZetaZeros_finite
      (isCompact_closedBall (0 : ℂ) ((n : ℝ) + 1))
  letI : Fintype K := hK.fintype
  let embed : (ZeroHeightShellSetV1 n) → K := fun rho =>
    ⟨rho.1.1, by
      have hstrip :=
        riemann_zeta_nontrivial_zero_critical_strip_v1 rho.1.2.1 rho.1.2.2
      have hre_nonneg : 0 ≤ rho.1.1.re := hstrip.1.le
      have hre_le : rho.1.1.re ≤ 1 := hstrip.2.le
      have hshell : ZeroHeightShellIndexV1 rho.1 = n := rho.2
      have hceil : |rho.1.1.im| ≤ (Nat.ceil |rho.1.1.im| : ℝ) :=
        Nat.le_ceil |rho.1.1.im|
      have him_le : |rho.1.1.im| ≤ (n : ℝ) := by
        rw [show Nat.ceil |rho.1.1.im| = n by
          simpa [ZeroHeightShellIndexV1] using hshell] at hceil
        exact hceil
      constructor
      · simp only [Metric.mem_closedBall, dist_zero_right]
        calc
          ‖rho.1.1‖ ≤ |rho.1.1.re| + |rho.1.1.im| :=
            Complex.norm_le_abs_re_add_abs_im rho.1.1
          _ = rho.1.1.re + |rho.1.1.im| := by rw [abs_of_nonneg hre_nonneg]
          _ ≤ 1 + (n : ℝ) := add_le_add hre_le him_le
          _ = (n : ℝ) + 1 := by ring
      · exact mem_riemannZetaZeros.mpr rho.1.2.1⟩
  exact Finite.of_injective embed (by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : K => z.1) hab)

/-- Finite norm-mass of the `n`-th canonical height shell. The expression is a
`tsum` over a finite subtype; finiteness is proved above. -/
def ZeroHeightShellMassV1 (f : ℝ → ℂ) (n : ℕ) : ℝ :=
  ∑' rho : ZeroHeightShellSetV1 n, ‖WeilZeroIndexSummandV1 f rho.1‖

private theorem zero_height_shell_partition_v1 :
    ∀ rho : RiemannNontrivialZeroIndexV2,
      ∃! n : ℕ, rho ∈ ZeroHeightShellSetV1 n := by
  intro rho
  refine ⟨ZeroHeightShellIndexV1 rho, ?_, ?_⟩
  · change ZeroHeightShellIndexV1 rho = ZeroHeightShellIndexV1 rho
    rfl
  · intro n hn
    change ZeroHeightShellIndexV1 rho = n at hn
    exact hn.symm

/-- Global absolute/norm summability of the zero-side summand is equivalent to
summability of the sequence of finite shell norm-masses. -/
theorem zero_norm_summable_iff_shell_mass_v1 (f : ℝ → ℂ) :
    Summable
        (fun rho : RiemannNontrivialZeroIndexV2 =>
          ‖WeilZeroIndexSummandV1 f rho‖) ↔
      Summable (ZeroHeightShellMassV1 f) := by
  have hpart :=
    summable_partition
      (f := fun rho : RiemannNontrivialZeroIndexV2 =>
        ‖WeilZeroIndexSummandV1 f rho‖)
      (s := ZeroHeightShellSetV1)
      (fun _ => norm_nonneg _)
      zero_height_shell_partition_v1
  constructor
  · intro h
    exact (hpart.mp h).2
  · intro hmass
    apply hpart.mpr
    refine ⟨?_, hmass⟩
    intro n
    letI : Fintype (ZeroHeightShellSetV1 n) :=
      (zero_height_shell_finite_v1 n).fintype
    exact (hasSum_fintype _).summable

/-- Summability of the finite shell masses is a sufficient certificate for
unconditional summability of the complex zero-side summand. -/
theorem zero_summable_of_shell_mass_v1
    {f : ℝ → ℂ} (h : Summable (ZeroHeightShellMassV1 f)) :
    Summable (WeilZeroIndexSummandV1 f) := by
  exact Summable.of_norm ((zero_norm_summable_iff_shell_mass_v1 f).mpr h)

/-- A summable shell-mass series therefore supplies an actual witness for the
already verified symmetric-height limit contract. -/
theorem shell_mass_implies_height_limit_exists_v1
    {f : ℝ → ℂ} (h : Summable (ZeroHeightShellMassV1 f)) :
    WeilZeroHeightLimitExistsV1 f := by
  have hsum : Summable (WeilZeroIndexSummandV1 f) :=
    zero_summable_of_shell_mass_v1 h
  refine ⟨∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1 f rho, ?_⟩
  exact hasSum_implies_height_limit_v1 hsum.hasSum

#check ZeroHeightShellIndexV1
#check ZeroHeightShellSetV1
#check zero_height_shell_finite_v1
#check ZeroHeightShellMassV1
#check zero_norm_summable_iff_shell_mass_v1
#check zero_summable_of_shell_mass_v1
#check shell_mass_implies_height_limit_exists_v1
#print axioms zero_height_shell_finite_v1
#print axioms zero_norm_summable_iff_shell_mass_v1
#print axioms zero_summable_of_shell_mass_v1
#print axioms shell_mass_implies_height_limit_exists_v1
