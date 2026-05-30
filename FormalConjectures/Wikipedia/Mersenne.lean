/-
Copyright 2025 The Formal Conjectures Authors.

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
# Conjectures about Mersenne primes

*References:*
- [Wikipedia: Mersenne conjectures](https://en.wikipedia.org/wiki/Mersenne_conjectures)
- [Wikipedia: Catalan's Mersenne conjecture](https://en.wikipedia.org/wiki/Catalan%27s_Mersenne_conjecture)
- [MathWorld: Catalan-Mersenne Number](https://mathworld.wolfram.com/Catalan-MersenneNumber.html)
-/

namespace Mersenne

namespace Nat

/--
A Wagstaff prime is a prime number of the form $(2^p+1)/3$.
-/
def GivesWagstaffPrime (p : ℕ) : Prop :=
  Odd p ∧ Nat.Prime ((2^p + 1) / 3)

/--
Holds when there is exists a number `k` such that $p = 2^k \\pm 1$ or $p = 4^k \\pm 3$.
-/
def IsSpecialForm (p : ℕ) : Prop :=
  ∃ k : ℕ, p = 2^k + 1 ∨ p = 2^k - 1 ∨ p = 4^k + 3 ∨ p = 4^k - 3

end Nat

open Mersenne

/--
The Catalan-Mersenne numbers, defined recursively by $c_0 = 2$ and
$c_{n+1} = 2^{c_n} - 1$.
-/
def catalanMersenne : ℕ → ℕ
  | 0 => 2
  | n + 1 => 2 ^ catalanMersenne n - 1

/--
A natural number `p` satisfies the statement of the New Mersenne Conjecture if whenever
two of the following conditions hold,
then all three must hold:
1. $2^p-1$ is prime
2. $(2^p+1)/3$ is prime
3. Exists a number `k` such that $p = 2^k \\pm 1$ or $p = 4^k \\pm 3$
-/
def NewMersenneConjectureStatement (p : ℕ) : Prop :=
  ((mersenne p).Prime ∧ p.GivesWagstaffPrime → p.IsSpecialForm) ∧
  ((mersenne p).Prime ∧ p.IsSpecialForm → p.GivesWagstaffPrime) ∧
  (p.GivesWagstaffPrime ∧ p.IsSpecialForm → (mersenne p).Prime)

/--
For any odd natural number `p` if two of the following conditions hold,
then all three must hold:
1. $2^p-1$ is prime
2. $(2^p+1)/3$ is prime
3. Exists a number `k` such that $p = 2^k \\pm 1$ or $p = 4^k \\pm 3$
-/
@[category research open, AMS 11]
theorem new_mersenne_conjecture (p : ℕ) (hp : Odd p) :
    NewMersenneConjectureStatement p := by
  sorry

/-- It suffices to check this conjecture for primes -/
@[category textbook, AMS 11]
theorem new_mersenne_conjecture_of_prime :
    (∀ p, p.Prime → NewMersenneConjectureStatement p) →
    ∀ p, Odd p → NewMersenneConjectureStatement p := by
  intro H p hp_odd
  by_cases hp_prime : p.Prime
  · exact H p hp_prime
  -- For odd composite (or `p = 1`) the antecedents `(mersenne p).Prime` and
  -- `p.GivesWagstaffPrime` are both false, so all three implications hold
  -- vacuously.
  have hF1 : ¬ (mersenne p).Prime := fun h => hp_prime h.of_mersenne
  have hF2 : ¬ Nat.GivesWagstaffPrime p := by
    rintro ⟨_, hP⟩
    by_cases hp1 : p = 1
    · subst hp1; norm_num at hP
    have hp_ne2 : p ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) hp_odd
    have hp_ge3 : 3 ≤ p := by have := hp_odd.pos; omega
    set q := p.minFac
    have hq_prime : q.Prime := Nat.minFac_prime hp1
    have hq_lt : q < p := (Nat.not_prime_iff_minFac_lt (by omega)).mp hp_prime
    have hq_dvd : q ∣ p := Nat.minFac_dvd p
    have hq_ne2 : q ≠ 2 := fun h =>
      Nat.not_even_iff_odd.mpr hp_odd (even_iff_two_dvd.mpr (h ▸ hq_dvd))
    have hq_odd : Odd q := hq_prime.odd_of_ne_two hq_ne2
    have hq_ge3 : 3 ≤ q := by have := hq_prime.two_le; omega
    obtain ⟨s, hs⟩ := hq_dvd
    have hs_odd : Odd s := (Nat.odd_mul.mp (hs ▸ hp_odd)).2
    -- `(2^q + 1) ∣ (2^p + 1)` from `Odd.nat_add_dvd_pow_add_pow` with `s` odd.
    have hpow_dvd : 2 ^ q + 1 ∣ 2 ^ p + 1 := by
      have h := Odd.nat_add_dvd_pow_add_pow (x := 2 ^ q) (y := 1) hs_odd
      simp only [one_pow, ← pow_mul] at h
      rw [← hs] at h; exact h
    -- `3 ∣ 2^q + 1` is the same lemma at `x = 2, y = 1`.
    have h3q : 3 ∣ 2 ^ q + 1 := by
      simpa using Odd.nat_add_dvd_pow_add_pow (x := 2) (y := 1) hq_odd
    have h3p : 3 ∣ 2 ^ p + 1 := h3q.trans hpow_dvd
    obtain ⟨k, hk⟩ := hpow_dvd
    set d := (2 ^ q + 1) / 3
    have hd_dvd : d ∣ (2 ^ p + 1) / 3 :=
      ⟨k, by rw [hk, mul_comm (2 ^ q + 1) k, Nat.mul_div_assoc k h3q, mul_comm]⟩
    have h8 : 8 ≤ 2 ^ q :=
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hq_ge3
    have hd_ge3 : 3 ≤ d := by show 3 ≤ (2 ^ q + 1) / 3; omega
    have hd_lt : d < (2 ^ p + 1) / 3 := by
      obtain ⟨a, ha⟩ := h3q
      obtain ⟨b, hb⟩ := h3p
      have hpow : 2 ^ q < 2 ^ p := Nat.pow_lt_pow_right (by norm_num) hq_lt
      show (2 ^ q + 1) / 3 < (2 ^ p + 1) / 3
      rw [ha, hb, Nat.mul_div_cancel_left _ (by norm_num : (0:ℕ) < 3),
          Nat.mul_div_cancel_left _ (by norm_num : (0:ℕ) < 3)]
      omega
    rcases hP.eq_one_or_self_of_dvd d hd_dvd with h | h <;> omega
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hA, _⟩; exact absurd hA hF1
  · rintro ⟨hA, _⟩; exact absurd hA hF1
  · rintro ⟨hB, _⟩; exact absurd hB hF2

/-- The New Mersenne Conjecture statement holds for odd primes. -/
@[category research open, AMS 11]
theorem new_mersenne_conjecture.variants.prime (p : ℕ) (hp : p.Prime) (h : Odd p) :
    NewMersenneConjectureStatement p := by
  sorry

/--
Are there infinitely many Mersenne primes?
-/
@[category research open, AMS 11]
theorem infinitely_many_mersenne_primes :
  answer(sorry) ↔ Set.Infinite { p : ℕ | (mersenne p).Prime } := by
    sorry

/--
The first five Catalan-Mersenne numbers $c_0, \ldots, c_4$ are known to be prime.
Catalan conjectured that they are prime "up to a certain limit".
Are all Catalan-Mersenne numbers $c_n$ with $n \geq 5$ prime?
-/
@[category research open, AMS 11]
theorem catalans_mersenne_conjecture :
    answer(sorry) ↔ ∀ n ≥ 5, Nat.Prime (catalanMersenne n) := by
  sorry

end Mersenne
