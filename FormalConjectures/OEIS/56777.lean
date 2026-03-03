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
@[category undergraduate, AMS 11]
theorem a_of_comesFromPrimeQuadruple {n : ℕ} (h : ComesFromPrimeQuadruple n) : a n := by
  sorry

/-- All members of the sequence A56777 come from prime quadruples. -/
@[category research open, AMS 11]
theorem comesFromPrimeQuadruple_of_a {n : ℕ} (h : a n) : ComesFromPrimeQuadruple n := by
  sorry

/-- Numbers coming from prime quadruples satisfy $n \equiv 65 \pmod{72}$.

**Proof sketch:** Any prime quadruple $(p, p+2, p+6, p+8)$ with all entries prime must have
$p \geq 5$ and $p \equiv 5 \pmod{6}$ (since $p$ is an odd prime with $p \not\equiv 1 \pmod 3$,
as that would force $3 \mid (p+2)$). Writing $p = 6k+5$, we have
$p(p+8) = (6k+5)(6k+13) = 36k(k+3) + 65$. Since $k(k+3)$ is always even
(one of $k, k+3$ is even), we get $p(p+8) = 72m + 65$ for some $m \geq 0$. -/
@[category undergraduate, AMS 11]
theorem mod_72_of_comesFromPrimeQuadruple {n : ℕ} (h : ComesFromPrimeQuadruple n) :
    n % 72 = 65 := by
  obtain ⟨p, hp, hp2, hp6, hp8, hn⟩ := h
  subst hn
  -- p ≠ 2: since if p = 2 then p+2 = 4 is not prime
  have hp_ne2 : p ≠ 2 := by
    intro heq; subst heq; exact absurd hp2 (by decide)
  -- p ≠ 3: since if p = 3 then p+6 = 9 = 3² is not prime
  have hp_ne3 : p ≠ 3 := by
    intro heq; subst heq; exact absurd hp6 (by decide)
  -- 2 ∤ p: p is prime and ≠ 2
  have hp_not2dvd : ¬ 2 ∣ p := by
    intro h2
    rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h
    · norm_num at h
    · exact hp_ne2 h.symm
  -- 3 ∤ p: p is prime and ≠ 3
  have hp_not3dvd : ¬ 3 ∣ p := by
    intro h3
    rcases hp.eq_one_or_self_of_dvd 3 h3 with h | h
    · norm_num at h
    · exact hp_ne3 h.symm
  -- 3 ∤ (p+2): p+2 is prime; if 3 ∣ (p+2) then p+2 = 3 so p = 1, contradicting p prime
  have hp2_not3dvd : ¬ 3 ∣ (p + 2) := by
    intro h3
    rcases hp2.eq_one_or_self_of_dvd 3 h3 with h | h
    · norm_num at h
    · linarith [hp.two_le]
  -- p % 2 = 1 (p is odd)
  have hp_mod2 : p % 2 = 1 := by
    have h0 : p % 2 ≠ 0 := fun h0 => hp_not2dvd (Nat.dvd_of_mod_eq_zero h0)
    omega
  -- p % 3 = 2: neither 0 (3 ∤ p) nor 1 (3 ∤ p+2, since p%3=1 → (p+2)%3=0)
  have hp_mod3 : p % 3 = 2 := by
    have h1 : p % 3 ≠ 0 := fun h0 => hp_not3dvd (Nat.dvd_of_mod_eq_zero h0)
    have h2 : (p + 2) % 3 ≠ 0 := fun h0 => hp2_not3dvd (Nat.dvd_of_mod_eq_zero h0)
    omega
  -- Decompose: p = 6k + 5 for k = p / 6
  set k := p / 6
  have hp_eq : p = 6 * k + 5 := by omega
  -- k * (k + 3) is even: if k even then 2 ∣ k; if k odd then k+3 is even so 2 ∣ k+3
  have h_even : 2 ∣ k * (k + 3) := by
    rcases Nat.even_or_odd k with ⟨r, hr⟩ | ⟨r, hr⟩
    · -- k = r + r (even), so 2 ∣ k
      exact (Nat.dvd_of_mod_eq_zero (by omega)).mul_right (k + 3)
    · -- k = 2r + 1 (odd), so k + 3 = 2(r+2) is even
      exact (Nat.dvd_of_mod_eq_zero (by omega)).mul_left k
  obtain ⟨m, hm⟩ := h_even
  -- Key identity: (6k+5)(6k+13) = 36·k·(k+3) + 65 = 72m + 65
  have h_main : p * (p + 8) = 72 * m + 65 := by
    rw [hp_eq]
    have step : (6 * k + 5) * (6 * k + 5 + 8) = 36 * (k * (k + 3)) + 65 := by ring
    linarith
  omega

/-- Numbers coming from prime quadruples satisfy $n \equiv 9 \pmod{100}$. -/
@[category undergraduate, AMS 11]
theorem mod_100_of_comesFromPrimeQuadruple {n : ℕ} (h : ComesFromPrimeQuadruple n) :
    n % 100 = 9 := by
  sorry

end OeisA56777
