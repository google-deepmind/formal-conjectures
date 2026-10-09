import WeilCriterionCompactSmoothV1
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
AEGIS Ω — finite prime-power support on the existing Weil test-function class.

Compact support contained in the positive half-line bounds both the support and
its reciprocal image. Consequently both evaluations in `WeilPrimeTermV1`
vanish above one finite cutoff. This proves actual summability of the existing
prime term, independently of any zero-counting or explicit-formula identity.

EXPLICIT_FORMULA_THEOREM_OPEN
WEIL_NEGATIVITY_OPEN
RH_EQUIVALENCE_OPEN
-/

open Set Function

set_option autoImplicit false

noncomputable section

/-- Positive compact support supplies a common real cutoff for a function and
its reciprocal evaluation. Smoothness is not needed for this statement. -/
theorem weil_eventually_zero_and_inv_of_compact_positive_support_v1
    (f : ℝ → ℂ) (hf : HasCompactSupport f)
    (hpos : tsupport f ⊆ Set.Ioi 0) :
    ∃ R : ℝ, 2 ≤ R ∧ ∀ x : ℝ, R ≤ x → f x = 0 ∧ f x⁻¹ = 0 := by
  have hK : IsCompact (tsupport f) := hf
  have hinv : ContinuousOn (fun x : ℝ => x⁻¹) (tsupport f) :=
    continuousOn_id.inv₀ (fun x hx => ne_of_gt (hpos hx))
  obtain ⟨A, hA⟩ := hK.bddAbove
  obtain ⟨B, hB⟩ := (hK.image_of_continuousOn hinv).bddAbove
  let R : ℝ := max 2 (max A B + 1)
  have hAR : A < R := calc
    A ≤ max A B := le_max_left _ _
    _ < max A B + 1 := by linarith
    _ ≤ R := le_max_right _ _
  have hBR : B < R := calc
    B ≤ max A B := le_max_right _ _
    _ < max A B + 1 := by linarith
    _ ≤ R := le_max_right _ _
  refine ⟨R, le_max_left _ _, ?_⟩
  intro x hx
  constructor
  · apply image_eq_zero_of_notMem_tsupport
    intro hmem
    exact (not_le_of_gt (lt_of_lt_of_le hAR hx)) (hA hmem)
  · apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have hxin : x ∈ (fun y : ℝ => y⁻¹) '' tsupport f :=
      ⟨x⁻¹, hmem, inv_inv x⟩
    exact (not_le_of_gt (lt_of_lt_of_le hBR hx)) (hB hxin)

/-- The common real cutoff specialized to the repository's existing class. -/
theorem weil_compact_smooth_eventually_zero_and_inv_v1
    (f : WeilCompactSmoothGV1) :
    ∃ R : ℝ, 2 ≤ R ∧ ∀ x : ℝ, R ≤ x → f.1 x = 0 ∧ f.1 x⁻¹ = 0 :=
  weil_eventually_zero_and_inv_of_compact_positive_support_v1
    f.1 f.2.2.1 f.2.2.2

/-- The existing prime-power term vanishes at every sufficiently large index. -/
theorem weil_compact_smooth_prime_term_cutoff_v1
    (f : WeilCompactSmoothGV1) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → WeilPrimeTermV1 f.1 n = 0 := by
  obtain ⟨R, _, hR⟩ := weil_compact_smooth_eventually_zero_and_inv_v1 f
  obtain ⟨N, hN⟩ := exists_nat_gt R
  refine ⟨N, ?_⟩
  intro n hn
  have hnR : R ≤ ((n + 1 : ℕ) : ℝ) := by
    apply le_trans hN.le
    exact_mod_cast hn.trans (Nat.le_succ n)
  obtain ⟨hlarge, hsmall⟩ := hR ((n + 1 : ℕ) : ℝ) hnR
  simp only [WeilPrimeTermV1, hlarge, hsmall, mul_zero, add_zero]

/-- There are only finitely many nonzero prime-power terms. -/
theorem weil_compact_smooth_prime_term_hasFiniteSupport_v1
    (f : WeilCompactSmoothGV1) :
    Function.HasFiniteSupport (WeilPrimeTermV1 f.1) := by
  classical
  obtain ⟨N, hN⟩ := weil_compact_smooth_prime_term_cutoff_v1 f
  refine (Finset.range N).finite_toSet.subset ?_
  intro n hn
  change WeilPrimeTermV1 f.1 n ≠ 0 at hn
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra hnot
  exact hn (hN n (Nat.le_of_not_gt hnot))

/-- The repository's prime-power series is summable for every compact-smooth
test function; no formal identity with the zero sum is asserted here. -/
theorem weil_compact_smooth_prime_summable_v1
    (f : WeilCompactSmoothGV1) : Summable (WeilPrimeTermV1 f.1) :=
  summable_of_hasFiniteSupport
    (weil_compact_smooth_prime_term_hasFiniteSupport_v1 f)

/-- The totalized prime `tsum` agrees with an actual finite sum. -/
theorem weil_compact_smooth_prime_sum_eq_finite_sum_v1
    (f : WeilCompactSmoothGV1) :
    ∃ N : ℕ, WeilPrimeSumV1 f.1 =
      ∑ n ∈ Finset.range N, WeilPrimeTermV1 f.1 n := by
  obtain ⟨N, hN⟩ := weil_compact_smooth_prime_term_cutoff_v1 f
  refine ⟨N, ?_⟩
  apply tsum_eq_sum
  intro n hn
  exact hN n (Nat.le_of_not_gt (by simpa using hn))
