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
module

public import FormalConjecturesUtil

/-!
# Conjectures about Mersenne primes

*References:*
- [Wikipedia: Mersenne conjectures](https://en.wikipedia.org/wiki/Mersenne_conjectures)
- [Wikipedia: Catalan's Mersenne conjecture](https://en.wikipedia.org/wiki/Catalan%27s_Mersenne_conjecture)
- [Wikipedia: List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics#Prime_numbers)
- [Wikipedia: Wieferich prime](https://en.wikipedia.org/wiki/Wieferich_prime)
- [MathWorld: Catalan-Mersenne Number](https://mathworld.wolfram.com/Catalan-MersenneNumber.html)
- A. Rotkiewicz, *Sur les nombres de Mersenne dépourvus de diviseurs carrés et sur les nombres
  naturels $n$, tels que $n^2 \mid 2^n - 2$*, Mat. Vesnik **2** (17) (1965), 78–80.
-/

@[expose] public section

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

/-- It suffices to check this conjecture for odd primes. The statement fails at `p = 2`:
`mersenne 2 = 3` is prime and `2 = 2 ^ 0 + 1`, but `2` gives no Wagstaff prime. -/
@[category textbook, AMS 11]
theorem new_mersenne_conjecture_of_prime :
    (∀ p, p.Prime → Odd p → NewMersenneConjectureStatement p) →
    ∀ p, Odd p → NewMersenneConjectureStatement p := by
  intro H p hp_odd
  by_cases hp_prime : p.Prime
  · exact H p hp_prime hp_odd
  suffices ¬Nat.GivesWagstaffPrime p by
    have hF1 : ¬(mersenne p).Prime := fun h => hp_prime h.of_mersenne
    refine ⟨?_, ?_, ?_⟩ <;> grind
  rintro ⟨_, hP⟩
  by_cases hp1 : p = 1
  · grind
  set q := p.minFac
  have hq_dvd : q ∣ p := Nat.minFac_dvd p
  have hq_ne2 : q ≠ 2 := fun h =>
    Nat.not_even_iff_odd.mpr hp_odd (even_iff_two_dvd.mpr (h ▸ hq_dvd))
  have hq_odd : Odd q := (Nat.minFac_prime hp1).odd_of_ne_two hq_ne2
  obtain ⟨s, hs⟩ := hq_dvd
  have hs_odd : Odd s := (Nat.odd_mul.mp (hs ▸ hp_odd)).2
  have hpow_dvd : 2 ^ q + 1 ∣ 2 ^ p + 1 := by
    grind [one_pow, ← pow_mul, Odd.nat_add_dvd_pow_add_pow (x := 2 ^ q) (y := 1) hs_odd]
  have h3q : 3 ∣ 2 ^ q + 1 := by
    grind [Odd.nat_add_dvd_pow_add_pow (x := 2) (y := 1)]
  have h3p : 3 ∣ 2 ^ p + 1 := h3q.trans hpow_dvd
  obtain ⟨k, hk⟩ := hpow_dvd
  set d := (2 ^ q + 1) / 3 with hd
  have hd_dvd : d ∣ (2 ^ p + 1) / 3 := by
    use k
    grind [mul_comm, Nat.mul_div_assoc, mul_comm]
  have h8 : 8 ≤ 2 ^ q := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) (by grind [(Nat.minFac_prime hp1).two_le])
  have hd_lt : d < (2 ^ p + 1) / 3 := by
    have hpow : 2 ^ q < 2 ^ p := by
      apply Nat.pow_lt_pow_right <;> grind [Nat.not_prime_iff_minFac_lt]
    grind [Nat.mul_div_cancel_left]
  rcases hP.eq_one_or_self_of_dvd d hd_dvd with h | h <;> grind

/-- The New Mersenne Conjecture statement holds for odd primes. -/
@[category research open, AMS 11]
theorem new_mersenne_conjecture.variants.prime (p : ℕ) (hp : p.Prime) (h : Odd p) :
    NewMersenneConjectureStatement p := by
  sorry

/--
Are there infinitely many Mersenne primes?
-/
@[category research open, question, AMS 11]
theorem infinitely_many_mersenne_primes :
  Set.Infinite { p : ℕ | (mersenne p).Prime } := by
    sorry

/--
The first five Catalan-Mersenne numbers $c_0, \ldots, c_4$ are known to be prime.
Catalan conjectured that they are prime "up to a certain limit".
Are all Catalan-Mersenne numbers $c_n$ with $n \geq 5$ prime?
-/
@[category research open, question, AMS 11]
theorem catalans_mersenne_conjecture :
    ∀ n ≥ 5, Nat.Prime (catalanMersenne n) := by
  sorry

/-- Checks `Squarefree (mersenne p)` at $p = 2, 3$ and at the first composite prime-exponent value
$M_{11} = 2047 = 23 \cdot 89$. -/
@[category test, AMS 11]
theorem squarefree_mersenne_small_primes :
    Squarefree (mersenne 2) ∧ Squarefree (mersenne 3) ∧ Squarefree (mersenne 11) := by
  decide +kernel

/-- Confirms that $M_0 = 0$ and $M_6 = 63 = 3^2 \cdot 7$ fail `Squarefree`, motivating the
restriction to prime exponents. -/
@[category test, AMS 11]
theorem not_squarefree_mersenne_zero_and_six :
    ¬ Squarefree (mersenne 0) ∧ ¬ Squarefree (mersenne 6) := by
  refine ⟨by rw [mersenne_zero]; exact not_squarefree_zero, fun h => ?_⟩
  have h3 : IsUnit (3 : ℕ) := h 3 ⟨7, rfl⟩
  rw [Nat.isUnit_iff] at h3
  omega

/-- At composite exponent $q = 6$, $3^2 \mid M_6 = 63$ even though $3$ is not a Wieferich prime. -/
@[category test, AMS 11]
theorem composite_index_sq_dvd_not_wieferich :
    3 ^ 2 ∣ mersenne 6 ∧ ¬ IsWieferichPrime 3 :=
  ⟨⟨7, rfl⟩, by decide⟩

/--
Is $M_p = 2^p - 1$ squarefree for every prime $p$?
-/
@[category research open, question, AMS 11]
theorem squarefree_mersenne_of_prime :
    ∀ p : ℕ, p.Prime → Squarefree (mersenne p) := by
  sorry

/--
For primes $q$ and $p$ with $p \mid M_q$, the square $p^2$ divides $M_q = 2^q - 1$ precisely when
`IsWieferichPrime p` holds. This is stated in the "Connection with Mersenne and Fermat primes"
section of the Wikipedia article on Wieferich primes: a prime divisor $p$ of $M_q$ is a Wieferich
prime if and only if $p^2$ divides $M_q$.
-/
@[category textbook, AMS 11]
theorem sq_dvd_mersenne_iff_isWieferichPrime
    {q p : ℕ} (hq : q.Prime) (hp : p.Prime) (hdvd : p ∣ mersenne q) :
    p ^ 2 ∣ mersenne q ↔ IsWieferichPrime p := by
  sorry

/--
Rotkiewicz's theorem (1965): if infinitely many values $M_n = 2^n - 1$ are squarefree, then
infinitely many primes fail `IsWieferichPrime`. Allowing $n$ to range over all natural numbers
rather than only primes gives the stronger form of this implication.
-/
@[category research solved, AMS 11]
theorem rotkiewicz_infinite_non_wieferich_of_squarefree_mersenne :
    {n : ℕ | Squarefree (mersenne n)}.Infinite →
      {p : ℕ | p.Prime ∧ ¬ IsWieferichPrime p}.Infinite := by
  sorry

end Mersenne
