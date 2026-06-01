/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import FormalConjectures.Util.ProblemImports

/-!
# Conjectures associated with A56777

A56777 lists composite numbers $n$ satisfying both $\varphi(n+12) = \varphi(n) + 12$ and
$\sigma(n+12) = \sigma(n) + 12$.

The conjectures state identities connecting A56777 and prime quadruples (A7530), as
well as congruences satisfied by the members of A56777.

*References:* [A56777](https://oeis.org/A56777)
-/

open Nat
open scoped ArithmeticFunction.sigma

namespace OeisA56777

/-- A composite number $n$ is in the sequence A56777 if it satisfies both
$\varphi(n+12) = \varphi(n) + 12$ and $\sigma(n+12) = \sigma(n) + 12$. -/
def a (n : ℕ) : Prop :=
  ¬n.Prime ∧ 1 < n ∧ totient (n + 12) = totient n + 12 ∧ σ 1 (n + 12) = σ 1 n + 12

/-- A number $n$ comes from a prime quadruple $(p, p+2, p+6, p+8)$ if
$n = p(p+8)$ for some prime $p$ where $p$, $p+2$, $p+6$, $p+8$ are all prime. -/
def ComesFromPrimeQuadruple (n : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ (p + 2).Prime ∧ (p + 6).Prime ∧ (p + 8).Prime ∧ n = p * (p + 8)

/-- $65$ is in the sequence A56777. -/
@[category test, AMS 11]
theorem a_65 : a 65 := by
  refine ⟨?_, by norm_num, ?_, ?_⟩
  · simp only [show (65 : ℕ) = 5 * 13 by norm_num]
    exact not_prime_mul (by norm_num) (by norm_num)
  · decide
  · decide

/-- $209$ is in the sequence A56777. -/
@[category test, AMS 11]
theorem a_209 : a 209 := by
  set_option maxRecDepth 1000 in
  refine ⟨?_, by norm_num, ?_, ?_⟩
  · simp only [show (209 : ℕ) = 11 * 19 by norm_num]
    exact not_prime_mul (by norm_num) (by norm_num)
  · decide
  · decide

/-- Numbers coming from prime quadruples are in the sequence A56777. -/
@[category textbook, AMS 11]
theorem a_of_comesFromPrimeQuadruple {n : ℕ} (h : ComesFromPrimeQuadruple n) : a n := by
  obtain ⟨p, hp, hp2, hp6, hp8, rfl⟩ := h
  -- n + 12 = p * (p+8) + 12 = (p+2) * (p+6)
  have hsum : p * (p + 8) + 12 = (p + 2) * (p + 6) := by ring
  -- coprimality facts between the four primes
  have hne_p_p8 : p ≠ p + 8 := by omega
  have hne_p2_p6 : p + 2 ≠ p + 6 := by omega
  have hcop1 : Nat.Coprime p (p + 8) := (Nat.coprime_primes hp hp8).mpr hne_p_p8
  have hcop2 : Nat.Coprime (p + 2) (p + 6) := (Nat.coprime_primes hp2 hp6).mpr hne_p2_p6
  refine ⟨?_, ?_, ?_, ?_⟩
  -- ¬ Prime (p * (p+8))
  · exact Nat.not_prime_mul hp.one_lt.ne' (by have := hp8.one_lt; omega)
  -- 1 < p * (p+8)
  · have h1 : 2 ≤ p := hp.two_le
    have h2 : 10 ≤ p + 8 := by omega
    nlinarith
  -- totient: φ((p+2)(p+6)) = φ(p(p+8)) + 12
  · rw [hsum, Nat.totient_mul hcop2, Nat.totient_mul hcop1,
        Nat.totient_prime hp, Nat.totient_prime hp2,
        Nat.totient_prime hp6, Nat.totient_prime hp8]
    zify [show 1 ≤ p from hp.one_lt.le, show 1 ≤ p + 2 by omega,
          show 1 ≤ p + 6 by omega, show 1 ≤ p + 8 by omega]
    ring
  -- sigma: σ₁((p+2)(p+6)) = σ₁(p(p+8)) + 12
  · rw [hsum, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop2,
        ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop1]
    have e1 : ArithmeticFunction.sigma 1 p = p + 1 := by
      have := ArithmeticFunction.sigma_one_apply_prime_pow (p := p) (i := 1) hp
      simpa using this
    have e2 : ArithmeticFunction.sigma 1 (p + 2) = (p + 2) + 1 := by
      have := ArithmeticFunction.sigma_one_apply_prime_pow (p := p + 2) (i := 1) hp2
      simpa using this
    have e6 : ArithmeticFunction.sigma 1 (p + 6) = (p + 6) + 1 := by
      have := ArithmeticFunction.sigma_one_apply_prime_pow (p := p + 6) (i := 1) hp6
      simpa using this
    have e8 : ArithmeticFunction.sigma 1 (p + 8) = (p + 8) + 1 := by
      have := ArithmeticFunction.sigma_one_apply_prime_pow (p := p + 8) (i := 1) hp8
      simpa using this
    rw [e1, e2, e6, e8]
    ring

/-- All members of the sequence A56777 come from prime quadruples. -/
@[category research open, AMS 11]
theorem comesFromPrimeQuadruple_of_a {n : ℕ} (h : a n) : ComesFromPrimeQuadruple n := by
  sorry

/-- Numbers coming from prime quadruples satisfy $n \equiv 65 \pmod{72}$. -/
@[category textbook, AMS 11]
theorem mod_72_of_comesFromPrimeQuadruple {n : ℕ} (h : ComesFromPrimeQuadruple n) :
    n % 72 = 65 := by
  obtain ⟨p, hp, hp2, hp6, hp8, rfl⟩ := h
  have hp5 : 5 ≤ p := by
    by_contra hlt; push_neg at hlt
    interval_cases p <;> simp_all (config := { decide := true })
  have h2 : ¬ (2 ∣ p) := by
    intro hdvd; cases hp.eq_one_or_self_of_dvd 2 hdvd with | inl h => omega | inr h => omega
  have h3 : ¬ (3 ∣ p) := by
    intro hdvd; cases hp.eq_one_or_self_of_dvd 3 hdvd with | inl h => omega | inr h => omega
  have hmod2 : p % 2 = 1 := by omega
  have hmod3 : p % 3 = 2 := by
    have hne1 : p % 3 ≠ 1 := by
      intro heq
      have h3dvd : 3 ∣ (p + 2) := ⟨p / 3 + 1, by omega⟩
      cases hp2.eq_one_or_self_of_dvd 3 h3dvd with | inl h => omega | inr h => omega
    omega
  have hmod6 : p % 6 = 5 := by omega
  set q := p / 6
  have hp_eq : p = 6 * q + 5 := by omega
  have hparity : 2 ∣ q * (q + 3) := by
    rcases Nat.even_or_odd q with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact dvd_mul_of_dvd_left ⟨r, by omega⟩ _
    · exact dvd_mul_of_dvd_right ⟨r + 2, by omega⟩ _
  obtain ⟨k, hk⟩ := hparity
  have h1 : p * (p + 8) = (6 * q + 5) * (6 * q + 13) := by congr 1; omega
  have h2 : (6 * q + 5) * (6 * q + 13) = 36 * (q * (q + 3)) + 65 := by ring
  have h3 : 36 * (q * (q + 3)) = 72 * k := by linarith
  have hprod : p * (p + 8) = 72 * k + 65 := by linarith
  omega

/-- Numbers coming from prime quadruples satisfy $n \equiv 9 \pmod{100}$,
except the first value "65". -/
@[category textbook, AMS 11]
theorem mod_100_of_comesFromPrimeQuadruple {n : ℕ} (h65 : 65 < n) (h : ComesFromPrimeQuadruple n) :
    n % 100 = 9 := by
  obtain ⟨p, hp, hp2, hp6, hp8, rfl⟩ := h
  have hp5 : 5 ≤ p := by
    by_contra hlt; push_neg at hlt
    interval_cases p <;> simp_all (config := { decide := true })
  have h2 : ¬ (2 ∣ p) := by
    intro hdvd; cases hp.eq_one_or_self_of_dvd 2 hdvd with | inl h => omega | inr h => omega
  have h3 : ¬ (3 ∣ p) := by
    intro hdvd; cases hp.eq_one_or_self_of_dvd 3 hdvd with | inl h => omega | inr h => omega
  have h5 : ¬ (5 ∣ p) := by
    intro hdvd; cases hp.eq_one_or_self_of_dvd 5 hdvd with | inl h => omega | inr h =>
      -- p = 5 → p*(p+8) = 65, but 65 < n = p*(p+8) is impossible
      subst h; omega
  have hmod30 : p % 30 = 11 := by
    have hmod2 : p % 2 = 1 := by omega
    have hmod3 : p % 3 = 2 := by
      have : p % 3 ≠ 1 := by
        intro heq; have : 3 ∣ (p + 2) := ⟨p / 3 + 1, by omega⟩
        cases hp2.eq_one_or_self_of_dvd 3 this with | inl h => omega | inr h => omega
      omega
    have hmod5 : p % 5 = 1 := by
      have hne2 : p % 5 ≠ 2 := by
        intro heq; have : 5 ∣ (p + 8) := ⟨p / 5 + 2, by omega⟩
        cases hp8.eq_one_or_self_of_dvd 5 this with | inl h => omega | inr h => omega
      have hne3 : p % 5 ≠ 3 := by
        intro heq; have : 5 ∣ (p + 2) := ⟨p / 5 + 1, by omega⟩
        cases hp2.eq_one_or_self_of_dvd 5 this with | inl h => omega | inr h => omega
      have hne4 : p % 5 ≠ 4 := by
        intro heq; have : 5 ∣ (p + 6) := ⟨p / 5 + 2, by omega⟩
        cases hp6.eq_one_or_self_of_dvd 5 this with | inl h => omega | inr h => omega
      omega
    omega
  set q := p / 30
  have hp_eq : p = 30 * q + 11 := by omega
  -- p*(p+8) = (30q+11)(30q+19) = 900*q*(q+1) + 30*(11+19)*q + 209
  -- = 900*q*(q+1) + 900*q + 209 ... let me just compute with ring
  have hparity : 2 ∣ q * (q + 1) := by
    rcases Nat.even_or_odd q with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact dvd_mul_of_dvd_left ⟨r, by omega⟩ _
    · exact dvd_mul_of_dvd_right ⟨r + 1, by omega⟩ _
  obtain ⟨k, hk⟩ := hparity
  have h1 : p * (p + 8) = (30 * q + 11) * (30 * q + 19) := by congr 1; omega
  have h2 : (30 * q + 11) * (30 * q + 19) = 900 * (q * (q + 1)) + 209 := by ring
  have h3 : 900 * (q * (q + 1)) = 1800 * k := by linarith
  have hprod : p * (p + 8) = 1800 * k + 209 := by linarith
  omega

end OeisA56777
