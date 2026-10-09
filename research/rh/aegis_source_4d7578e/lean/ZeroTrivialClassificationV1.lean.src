import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
AEGIS Ω — negative-integer trivial-zero classification v1.

This lane proves only the exact classification of Riemann-zeta zeros at points
`-n`, `n : ℕ`. It does not yet combine that classification with the separate
nonpositive-half-plane reduction, does not prove the full critical strip, and
does not prove RH.

NEGATIVE_INTEGER_PARITY_CLASSIFICATION_ONLY
LOWER_ZERO_LOCALIZATION_OPEN
FULL_CRITICAL_STRIP_OPEN
RH_EQUIVALENCE_OPEN
-/

open Complex

/-- Positive even-index Bernoulli numbers are nonzero.

The proof is intentionally bound to the pinned special-value formula for
`ζ(2k)` and the pinned nonvanishing theorem on `Re(s) ≥ 1`, rather than taking
Bernoulli nonvanishing as an unverified side assumption. -/
theorem bernoulli_two_mul_ne_zero_v1 (k : ℕ) (hk : k ≠ 0) :
    bernoulli (2 * k) ≠ 0 := by
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

/-- Riemann zeta does not vanish at a negative odd integer. -/
theorem riemann_zeta_neg_odd_ne_zero_v1 (k : ℕ) :
    riemannZeta (-(((2 * k + 1 : ℕ) : ℂ))) ≠ 0 := by
  rw [riemannZeta_neg_nat_eq_bernoulli (2 * k + 1)]
  apply div_ne_zero
  · apply mul_ne_zero
    · exact pow_ne_zero _ (by norm_num)
    · have hb : bernoulli (2 * (k + 1)) ≠ 0 :=
        bernoulli_two_mul_ne_zero_v1 (k + 1) (by omega)
      have hidx : (2 * k + 1) + 1 = 2 * (k + 1) := by omega
      rw [hidx]
      exact_mod_cast hb
  · exact_mod_cast (show (2 * k + 1) + 1 ≠ 0 by omega)

/-- Exact classification of Riemann-zeta zeros among the nonpositive integer
points represented as `-n`.

The zero points are exactly `-2, -4, -6, ...`, matching Mathlib's definition of
the trivial-zero exception used in `RiemannHypothesis`. -/
theorem riemann_zeta_neg_nat_zero_iff_trivial_v1 (n : ℕ) :
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
      · exact ((riemann_zeta_neg_odd_ne_zero_v1 k) hz).elim
  · rintro ⟨k, rfl⟩
    simpa [Nat.cast_mul, Nat.cast_add] using riemannZeta_neg_two_mul_nat_add_one k

#check bernoulli_two_mul_ne_zero_v1
#check riemann_zeta_neg_odd_ne_zero_v1
#check riemann_zeta_neg_nat_zero_iff_trivial_v1
#print axioms bernoulli_two_mul_ne_zero_v1
#print axioms riemann_zeta_neg_odd_ne_zero_v1
#print axioms riemann_zeta_neg_nat_zero_iff_trivial_v1
