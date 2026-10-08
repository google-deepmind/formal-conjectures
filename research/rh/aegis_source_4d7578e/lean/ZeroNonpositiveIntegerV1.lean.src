import Mathlib.NumberTheory.LSeries.ZetaZeros

/-!
AEGIS Ω — nonpositive-half-plane integer reduction for Riemann-zeta zeros v1.

This lane proves only that a Riemann-zeta zero with nonpositive real part must
lie at a nonpositive integer `-n`. It does not classify which negative integers
are zeros, prove the lower real-part bound for nontrivial zeros, prove the full
critical strip, an explicit formula, or RH.

NONPOSITIVE_ZERO_INTEGER_REDUCTION_ONLY
NEGATIVE_INTEGER_PARITY_CLASSIFICATION_OPEN
LOWER_ZERO_LOCALIZATION_OPEN
FULL_CRITICAL_STRIP_OPEN
RH_EQUIVALENCE_OPEN
-/

open Complex

/-- A zeta zero in the closed left half-plane must be a nonpositive integer.

Away from points `-n`, the pinned zeta functional equation sends a hypothetical
zero at `s` to a zero at `1-s`. If `Re(s) ≤ 0`, then `Re(1-s) ≥ 1`, contradicting
Mathlib's pinned nonvanishing theorem on that half-plane. -/
theorem riemann_zeta_zero_nonpos_is_neg_nat_v1
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

#check riemann_zeta_zero_nonpos_is_neg_nat_v1
#print axioms riemann_zeta_zero_nonpos_is_neg_nat_v1
