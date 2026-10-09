import WeilPrimeReindexV1
import WeilAutocorrelationClosureV1
import Mathlib.Tactic

/-!
AEGIS Ω — autocorrelation prime-side canonical real normal form.

This module composes the exact autocorrelation closure/reciprocal identity with
PR #501's canonical `m ≥ 2` prime reindex.  For the actual repository
multiplicative autocorrelation `A_g`, every positive-integer canonical prime
term becomes

  `Λ(m) * (A_g(m) + conj (A_g(m)))`,

hence an explicitly real term.  Compact support then turns the entire prime
side into a finite sum of these real canonical terms.

No explicit-formula identity, archimedean sign, global Weil positivity, or RH
is asserted.

EXPLICIT_FORMULA_IDENTITY_OPEN
ARCHIMEDEAN_SIGN_OPEN
GLOBAL_WEIL_SIGN_OPEN
RH_NOT_PROVEN
AUTHORITY_EFFECT_NONE
-/

open Set Function Complex
open scoped ArithmeticFunction ComplexConjugate

set_option autoImplicit false

noncomputable section

/-- Explicitly real canonical prime term for the repository autocorrelation. -/
def CanonicalWeilAutocorrelationPrimeRealTermV1
    (g : WeilCompactSmoothGV1) (m : ℕ) : ℂ :=
  ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) *
    (((2 * (WeilAutocorrelationV1 g (m : ℝ)).re : ℝ) : ℂ))

/-- The reciprocal-Jacobian identity collapses each positive canonical prime
term to `2 Λ(m) Re(A_g(m))`. -/
theorem canonical_weil_autocorrelation_prime_term_real_v1
    (g : WeilCompactSmoothGV1) (m : ℕ) (hm : 0 < m) :
    CanonicalWeilPrimeTermV1 (WeilAutocorrelationV1 g) m =
      CanonicalWeilAutocorrelationPrimeRealTermV1 g m := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hrec := weil_autocorrelation_reciprocal_v1 g (x := (m : ℝ)) hmR
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  unfold CanonicalWeilPrimeTermV1 CanonicalWeilAutocorrelationPrimeRealTermV1
  rw [hrec]
  simp [div_eq_mul_inv, hmC, mul_assoc, Complex.add_conj]

/-- Direct composition of autocorrelation closure with PR #501: the actual
prime side is a finite canonical `m=i+2` sum. -/
theorem weil_autocorrelation_prime_sum_eq_canonical_finite_sum_v1
    (g : WeilCompactSmoothGV1) :
    ∃ N : ℕ, WeilPrimeSumV1 (WeilAutocorrelationV1 g) =
      ∑ i ∈ Finset.range N,
        CanonicalWeilPrimeTailV1 (WeilAutocorrelationV1 g) i := by
  simpa only [weil_autocorrelation_compact_smooth_coe_v1] using
    (weil_prime_sum_eq_canonical_finite_sum_v1
      (WeilAutocorrelationCompactSmoothV1 g))

/-- Final prime-side normal form: the entire autocorrelation prime contribution
is a finite sum of explicitly real positive-integer terms.  This is a normal
form only; the real summands need not be nonnegative. -/
theorem weil_autocorrelation_prime_sum_eq_finite_real_sum_v1
    (g : WeilCompactSmoothGV1) :
    ∃ N : ℕ, WeilPrimeSumV1 (WeilAutocorrelationV1 g) =
      ∑ i ∈ Finset.range N,
        CanonicalWeilAutocorrelationPrimeRealTermV1 g (i + 2) := by
  obtain ⟨N, hN⟩ := weil_autocorrelation_prime_sum_eq_canonical_finite_sum_v1 g
  refine ⟨N, hN.trans ?_⟩
  apply Finset.sum_congr rfl
  intro i hi
  simpa [CanonicalWeilPrimeTailV1] using
    (canonical_weil_autocorrelation_prime_term_real_v1 g (i + 2) (by omega))

#print axioms canonical_weil_autocorrelation_prime_term_real_v1
#print axioms weil_autocorrelation_prime_sum_eq_canonical_finite_sum_v1
#print axioms weil_autocorrelation_prime_sum_eq_finite_real_sum_v1
