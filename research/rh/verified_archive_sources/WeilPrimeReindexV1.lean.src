import WeilPrimeSummabilityV1
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

/-!
AEGIS Ω — canonical reindex of the existing Weil prime term.

This module binds the existing Lean definition

  `WeilPrimeTermV1 f n`, with `m = n + 1`,

to the canonical positive-integer expression

  `Λ(m) * (f(m) + m⁻¹ * f(m⁻¹))`,

then removes the inert `m = 1` term and reindexes the remaining tail by
`m = i + 2`.  It does not prove an explicit-formula identity, any cross-prover
carrier equivalence, Weil positivity, or RH.

EXPLICIT_FORMULA_IDENTITY_OPEN
CROSS_PROVER_SEMANTIC_EQUIVALENCE_OPEN
GLOBAL_WEIL_SIGN_OPEN
RH_NOT_PROVEN
AUTHORITY_EFFECT_NONE
-/

open Set Function
open scoped ArithmeticFunction

set_option autoImplicit false

noncomputable section

/-- Canonical multiplicative prime term at a positive integer coordinate `m`. -/
def CanonicalWeilPrimeTermV1 (f : ℝ → ℂ) (m : ℕ) : ℂ :=
  ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) *
    (f (m : ℝ) + (1 / (m : ℂ)) * f (((m : ℝ))⁻¹))

/-- Canonical `m ≥ 2` tail, indexed by `i` with `m = i + 2`. -/
def CanonicalWeilPrimeTailV1 (f : ℝ → ℂ) (i : ℕ) : ℂ :=
  CanonicalWeilPrimeTermV1 f (i + 2)

/-- The canonical tail as an actual `tsum`. -/
def CanonicalWeilPrimeTailSumV1 (f : ℝ → ℂ) : ℂ :=
  ∑' i : ℕ, CanonicalWeilPrimeTailV1 f i

/-- The repository prime term is definitionally the canonical term at `m=n+1`. -/
theorem weil_prime_term_eq_canonical_succ_v1 (f : ℝ → ℂ) (n : ℕ) :
    WeilPrimeTermV1 f n = CanonicalWeilPrimeTermV1 f (n + 1) := by
  rfl

/-- The canonical `m=1` term is inert because `Λ(1)=0`. -/
theorem canonical_weil_prime_term_one_zero_v1 (f : ℝ → ℂ) :
    CanonicalWeilPrimeTermV1 f 1 = 0 := by
  simp [CanonicalWeilPrimeTermV1]

/-- Therefore the repository's leading sequence term `n=0` vanishes. -/
theorem weil_prime_term_zero_index_zero_v1 (f : ℝ → ℂ) :
    WeilPrimeTermV1 f 0 = 0 := by
  rw [weil_prime_term_eq_canonical_succ_v1]
  simpa using canonical_weil_prime_term_one_zero_v1 f

/-- After dropping `m=1`, `n=i+1` is exactly the canonical `m=i+2` term. -/
theorem weil_prime_term_tail_reindex_v1 (f : ℝ → ℂ) (i : ℕ) :
    WeilPrimeTermV1 f (i + 1) = CanonicalWeilPrimeTailV1 f i := by
  rw [weil_prime_term_eq_canonical_succ_v1]
  rfl

/-- The first tail coordinate is exactly the positive integer `m=2`. -/
theorem canonical_weil_prime_tail_zero_index_v1 (f : ℝ → ℂ) :
    CanonicalWeilPrimeTailV1 f 0 = CanonicalWeilPrimeTermV1 f 2 := by
  rfl

/-- Compact positive support makes the canonical `m≥2` tail eventually zero. -/
theorem canonical_weil_prime_tail_eventually_zero_v1
    (f : WeilCompactSmoothGV1) :
    ∃ N : ℕ, ∀ i : ℕ, N ≤ i → CanonicalWeilPrimeTailV1 f.1 i = 0 := by
  obtain ⟨N, hN⟩ := weil_compact_smooth_prime_term_cutoff_v1 f
  refine ⟨N, ?_⟩
  intro i hi
  rw [← weil_prime_term_tail_reindex_v1]
  exact hN (i + 1) (hi.trans (Nat.le_succ i))

/-- Hence the canonical tail has finite support. -/
theorem canonical_weil_prime_tail_hasFiniteSupport_v1
    (f : WeilCompactSmoothGV1) :
    Function.HasFiniteSupport (CanonicalWeilPrimeTailV1 f.1) := by
  classical
  obtain ⟨N, hN⟩ := canonical_weil_prime_tail_eventually_zero_v1 f
  refine (Finset.range N).finite_toSet.subset ?_
  intro i hi
  change CanonicalWeilPrimeTailV1 f.1 i ≠ 0 at hi
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra hnot
  exact hi (hN i (Nat.le_of_not_gt hnot))

/-- Finite support supplies summability of the canonical tail. -/
theorem canonical_weil_prime_tail_summable_v1
    (f : WeilCompactSmoothGV1) :
    Summable (CanonicalWeilPrimeTailV1 f.1) :=
  summable_of_hasFiniteSupport
    (canonical_weil_prime_tail_hasFiniteSupport_v1 f)

/-- Dropping the inert head gives equality with the canonical `m≥2` tail sum. -/
theorem weil_prime_sum_eq_canonical_tail_v1
    (f : WeilCompactSmoothGV1) :
    WeilPrimeSumV1 f.1 = CanonicalWeilPrimeTailSumV1 f.1 := by
  unfold WeilPrimeSumV1 CanonicalWeilPrimeTailSumV1
  have hs := weil_compact_smooth_prime_summable_v1 f
  calc
    (∑' n : ℕ, WeilPrimeTermV1 f.1 n) =
        (∑ n ∈ Finset.range 1, WeilPrimeTermV1 f.1 n) +
          ∑' i : ℕ, WeilPrimeTermV1 f.1 (i + 1) := by
            exact (hs.sum_add_tsum_nat_add 1).symm
    _ = ∑' i : ℕ, WeilPrimeTermV1 f.1 (i + 1) := by
          simp [weil_prime_term_zero_index_zero_v1]
    _ = ∑' i : ℕ, CanonicalWeilPrimeTailV1 f.1 i := by
          apply tsum_congr
          intro i
          exact weil_prime_term_tail_reindex_v1 f.1 i

/-- The canonical tail `tsum` is equal to an actual finite sum. -/
theorem canonical_weil_prime_tail_sum_eq_finite_sum_v1
    (f : WeilCompactSmoothGV1) :
    ∃ N : ℕ, CanonicalWeilPrimeTailSumV1 f.1 =
      ∑ i ∈ Finset.range N, CanonicalWeilPrimeTailV1 f.1 i := by
  obtain ⟨N, hN⟩ := canonical_weil_prime_tail_eventually_zero_v1 f
  refine ⟨N, ?_⟩
  unfold CanonicalWeilPrimeTailSumV1
  apply tsum_eq_sum
  intro i hi
  exact hN i (Nat.le_of_not_gt (by simpa using hi))

/-- Final consumer form: the repository prime sum is literally a finite sum
    of canonical `m=i+2` terms. -/
theorem weil_prime_sum_eq_canonical_finite_sum_v1
    (f : WeilCompactSmoothGV1) :
    ∃ N : ℕ, WeilPrimeSumV1 f.1 =
      ∑ i ∈ Finset.range N, CanonicalWeilPrimeTailV1 f.1 i := by
  obtain ⟨N, hN⟩ := canonical_weil_prime_tail_sum_eq_finite_sum_v1 f
  refine ⟨N, ?_⟩
  rw [weil_prime_sum_eq_canonical_tail_v1]
  exact hN
