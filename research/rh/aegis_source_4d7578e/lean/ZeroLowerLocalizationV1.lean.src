import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
AEGIS Ω — lower localization of nontrivial Riemann-zeta zeros v1.

This lane proves only that a Riemann-zeta zero which is not one of the standard
trivial zeros `-2, -4, -6, ...` has strictly positive real part. The
nontrivial-zero predicate is written in the same form used by the pinned
Formal Conjectures / Mathlib `RiemannHypothesis` target.

It does not prove the upper real-part bound in this source, does not compose a
full critical strip theorem, and does not prove RH.

LOWER_ZERO_LOCALIZATION_ONLY
FULL_CRITICAL_STRIP_OPEN
RH_EQUIVALENCE_OPEN
-/

open Complex

private theorem zero_nonpos_is_neg_nat_lower_local_v1
    {s : ℂ} (hz : riemannZeta s = 0) (hre : s.re ≤ 0) :
    ∃ n : ℕ, s = -n := by
  by_contra hneg
  have hnotnat : ∀ n : ℕ, s ≠ -n := by
    intro n hsn
    exact hneg ⟨n, hsn⟩
  have hs1 : s ≠ 1 := by
    intro hs
    subst s
    exact (not_le_of_gt (zero_lt_one : (0 : ℝ) < 1)) (by simpa using hre)
  have hzero_reflected : riemannZeta (1 - s) = 0 := by
    rw [riemannZeta_one_sub hnotnat hs1, hz, mul_zero]
  have hge : 1 ≤ (1 - s).re := by
    simpa [sub_eq_add_neg] using
      (le_add_of_nonneg_right (neg_nonneg.mpr hre) : (1 : ℝ) ≤ 1 + (-s.re))
  exact (riemannZeta_ne_zero_of_one_le_re hge) hzero_reflected

private theorem bernoulli_two_mul_ne_zero_lower_local_v1
    (k : ℕ) (hk : k ≠ 0) : bernoulli (2 * k) ≠ 0 := by
  intro hB
  have hzeta0 : riemannZeta (2 * (k : ℂ)) = 0 := by
    rw [riemannZeta_two_mul_nat hk, hB]
    simp
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
  have hge : (1 : ℝ) ≤ (2 * (k : ℂ)).re := by
    norm_num
    linarith
  exact (riemannZeta_ne_zero_of_one_le_re hge) hzeta0

private theorem zeta_neg_odd_ne_zero_lower_local_v1 (k : ℕ) :
    riemannZeta (-(((2 * k + 1 : ℕ) : ℂ))) ≠ 0 := by
  rw [riemannZeta_neg_nat_eq_bernoulli (2 * k + 1)]
  apply div_ne_zero
  · apply mul_ne_zero
    · exact pow_ne_zero _ (by norm_num)
    · have hb : bernoulli (2 * (k + 1)) ≠ 0 :=
        bernoulli_two_mul_ne_zero_lower_local_v1 (k + 1) (by omega)
      have hidx : (2 * k + 1) + 1 = 2 * (k + 1) := by omega
      rw [hidx]
      exact_mod_cast hb
  · exact_mod_cast (show (2 * k + 1) + 1 ≠ 0 by omega)

private theorem zeta_neg_nat_zero_iff_trivial_lower_local_v1 (n : ℕ) :
    riemannZeta (-(n : ℂ)) = 0 ↔ ∃ k : ℕ, n = 2 * (k + 1) := by
  constructor
  · intro hz
    by_cases hn : n = 0
    · subst n
      norm_num [riemannZeta_zero] at hz
    · rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
      · have hk : k ≠ 0 := by
          intro hk
          subst k
          simp at hn
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
        exact ⟨j, rfl⟩
      · exact ((zeta_neg_odd_ne_zero_lower_local_v1 k) hz).elim
  · rintro ⟨k, rfl⟩
    simpa [Nat.cast_mul, Nat.cast_add] using riemannZeta_neg_two_mul_nat_add_one k

private theorem zero_nonpos_is_trivial_lower_local_v1
    {s : ℂ} (hz : riemannZeta s = 0) (hre : s.re ≤ 0) :
    ∃ k : ℕ, s = -(2 : ℂ) * (k + 1) := by
  obtain ⟨n, hs⟩ := zero_nonpos_is_neg_nat_lower_local_v1 hz hre
  have hzn : riemannZeta (-(n : ℂ)) = 0 := by
    rw [← hs]
    exact hz
  obtain ⟨k, hnk⟩ := (zeta_neg_nat_zero_iff_trivial_lower_local_v1 n).mp hzn
  refine ⟨k, ?_⟩
  calc
    s = -(n : ℂ) := hs
    _ = -((2 * (k + 1) : ℕ) : ℂ) := by rw [hnk]
    _ = -(2 : ℂ) * (k + 1) := by push_cast; ring

/-- A nontrivial Riemann-zeta zero has strictly positive real part.

The nontriviality hypothesis is exactly the negative-even-integer exclusion
appearing in the pinned `RiemannHypothesis` target. -/
theorem riemann_zeta_nontrivial_zero_re_pos_v1
    {s : ℂ} (hz : riemannZeta s = 0)
    (hnontrivial : ¬ ∃ n : ℕ, s = -(2 : ℂ) * (n + 1)) :
    0 < s.re := by
  by_contra hpos
  have hre : s.re ≤ 0 := le_of_not_gt hpos
  exact hnontrivial (zero_nonpos_is_trivial_lower_local_v1 hz hre)

#check riemann_zeta_nontrivial_zero_re_pos_v1
#print axioms riemann_zeta_nontrivial_zero_re_pos_v1
