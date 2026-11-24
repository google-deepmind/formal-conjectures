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
module

public import FormalConjecturesUtil

/-!
# Proth primes

A *Proth number* is an integer $N = k \cdot 2^n + 1$ where $k$ is odd and $1 \le k < 2^n$. A Proth
number that is prime is called a *Proth prime*. Proth proved in 1878 that a Proth number $N$ is
prime if and only if $-1$ is an $((N - 1)/2)$-th power modulo $N$. It remains open whether
infinitely many Proth primes exist, and in particular whether any fixed odd multiplier such as
$k = 3$ produces infinitely many primes $3 \cdot 2^n + 1$.

*References:*
- [Wikipedia: Proth prime](https://en.wikipedia.org/wiki/Proth_prime)
- [Wikipedia: Thabit number](https://en.wikipedia.org/wiki/Thabit_number)
- [OEIS A080076](https://oeis.org/A080076)
- [OEIS A002253](https://oeis.org/A002253)
- [Pr1878] Proth, F. (1878). *Théorèmes sur les nombres premiers*, C. R. Acad. Sci. Paris 87, 926.
- [CP05] Crandall, R. and Pomerance, C. (2005). *Prime Numbers: A Computational Perspective*, 2nd
  ed., Springer, New York.
-/

@[expose] public section

namespace ProthPrime

/-- An integer $N$ is a **Proth number** if $N = k \cdot 2^n + 1$ for some odd $k$ and $n \ge 1$
with $k < 2^n$. -/
def IsProthNumber (N : ℕ) : Prop :=
  ∃ k n : ℕ, Odd k ∧ 1 ≤ n ∧ k < 2 ^ n ∧ N = k * 2 ^ n + 1

/-- A prime integer that is also a Proth number ([OEIS A080076](https://oeis.org/A080076)). -/
def IsProthPrime (N : ℕ) : Prop :=
  N.Prime ∧ IsProthNumber N

/-- $13 = 3 \cdot 2^2 + 1$ is a Proth prime. -/
@[category test, AMS 11]
theorem isProthPrime_thirteen : IsProthPrime 13 :=
  ⟨by decide, 3, 2, ⟨1, rfl⟩, by omega, by omega, by omega⟩

/-- $41 = 5 \cdot 2^3 + 1$ is a Proth prime. -/
@[category test, AMS 11]
theorem isProthPrime_forty_one : IsProthPrime 41 :=
  ⟨by decide, 5, 3, ⟨2, rfl⟩, by omega, by omega, by omega⟩

/-- $9 = 1 \cdot 2^3 + 1$ is a composite Proth number. -/
@[category test, AMS 11]
theorem isProthNumber_nine_and_not_prime : IsProthNumber 9 ∧ ¬ IsProthPrime 9 :=
  ⟨⟨1, 3, ⟨0, rfl⟩, by omega, by omega, by omega⟩, fun h => absurd h.1 (by decide)⟩

/-- $7 = 3 \cdot 2^1 + 1$ is prime, but is not a Proth number because $3 \not< 2^1$. -/
@[category test, AMS 11]
theorem not_isProthNumber_seven : ¬ IsProthNumber 7 := by
  rintro ⟨k, n, hk, _, _, heq⟩
  have hn_le : n ≤ 2 := by
    by_contra h
    have hpow : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
    have hk1 : 1 ≤ k := hk.pos
    nlinarith
  interval_cases n <;> omega

/-- If an odd multiplier $k$ is a Sierpiński number (`Nat.IsSierpinskiNumber`), then
$k \cdot 2^n + 1$ is never a Proth prime for any $n \in \mathbb{N}$. -/
@[category API, AMS 11]
theorem not_isProthPrime_of_isSierpinskiNumber {k : ℕ} (hk : k.IsSierpinskiNumber) (n : ℕ) :
    ¬ IsProthPrime (k * 2 ^ n + 1) :=
  fun h => (hk.2 n).2 h.1

/--
**Proth's primality theorem** [Pr1878, CP05]: a Proth number $N = k \cdot 2^n + 1$ ($k$ odd,
$k < 2^n$) is prime precisely when some residue $a \in \mathbb{Z}/N\mathbb{Z}$ satisfies
$a^{(N - 1) / 2} = -1$.
-/
@[category textbook, AMS 11]
theorem proth_primality_criterion (N : ℕ) (hN : IsProthNumber N) :
    N.Prime ↔ ∃ a : ZMod N, a ^ ((N - 1) / 2) = -1 := by
  obtain ⟨k, n, hk, hn, hkn, hNeq⟩ := hN
  have h2n : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hpos : 0 < 2 ^ (n - 1) := by positivity
  have hk1 : 1 ≤ k := hk.pos
  have hodd : N % 2 = 1 := by
    rw [hNeq, h2n, ← mul_assoc, mul_comm k 2, mul_assoc]
    omega
  have hN3 : 3 ≤ N := by
    have : 1 * 2 ≤ k * 2 ^ n := Nat.mul_le_mul hk1 (by omega)
    omega
  constructor
  · -- A quadratic non-residue `a` satisfies `a ^ ((N - 1) / 2) = -1` by Euler's criterion.
    intro hp
    have : Fact N.Prime := ⟨hp⟩
    obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod N) (by
      rw [ZMod.ringChar_zmod_n]
      omega)
    have ha0 : a ≠ 0 := fun h => ha (h ▸ IsSquare.zero)
    refine ⟨a, ?_⟩
    rw [show (N - 1) / 2 = N / 2 by omega]
    exact (ZMod.pow_div_two_eq_neg_one_or_one _ ha0).resolve_left
      fun h1 => ha ((ZMod.euler_criterion _ ha0).2 h1)
  · -- Every prime factor `q` of `N` satisfies `2 ^ n ∣ q - 1`, so `q ^ 2 > N`.
    rintro ⟨a, ha⟩
    by_contra hnp
    have hq : N.minFac.Prime := Nat.minFac_prime (by omega)
    have hqN : N.minFac ∣ N := Nat.minFac_dvd N
    have hq2 : N.minFac ^ 2 ≤ N := Nat.minFac_sq_le_self (by omega) hnp
    generalize N.minFac = q at hq hqN hq2
    have hqodd : q ≠ 2 := fun h => by
      rw [h] at hqN
      omega
    have : Fact q.Prime := ⟨hq⟩
    have : Fact (2 < q) := ⟨lt_of_le_of_ne hq.two_le (Ne.symm hqodd)⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hexp : (N - 1) / 2 = k * 2 ^ (n - 1) := by
      rw [hNeq, Nat.add_sub_cancel, h2n, ← mul_assoc, mul_comm k 2, mul_assoc,
        Nat.mul_div_cancel_left _ (by norm_num)]
    -- The image `b` of `a ^ k` in `ZMod q` has order exactly `2 ^ n`.
    set b : ZMod q := (ZMod.castHom hqN (ZMod q) a) ^ k with hb
    have hb1 : b ^ 2 ^ (n - 1) = -1 := by
      rw [hb, ← pow_mul, ← hexp, ← map_pow, ha, map_neg, map_one]
    have hb2 : b ^ 2 ^ (n - 1 + 1) = 1 := by
      rw [pow_succ, pow_mul, hb1]
      norm_num
    have hord : orderOf b = 2 ^ (n - 1 + 1) :=
      orderOf_eq_prime_pow (by rw [hb1]; exact ZMod.neg_one_ne_one) hb2
    have hb0 : b ≠ 0 := fun h => by
      rw [h, zero_pow (by positivity)] at hb2
      exact zero_ne_one hb2
    have hdvd : 2 ^ (n - 1 + 1) ∣ q - 1 := by
      rw [← hord]
      exact orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hb0)
    rw [show n - 1 + 1 = n by omega] at hdvd
    have hle : 2 ^ n ≤ q - 1 := Nat.le_of_dvd (by have := hq.two_le; omega) hdvd
    have hq' : 2 ^ n + 1 ≤ q := by have := hq.two_le; omega
    have hsq : (2 ^ n + 1) ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq' 2
    have hlt : N < (2 ^ n + 1) ^ 2 := by
      rw [hNeq]
      nlinarith [Nat.mul_lt_mul_of_pos_right hkn (by positivity : 0 < 2 ^ n)]
    exact absurd (hlt.trans_le (hsq.trans hq2)) (lt_irrefl _)

/--
There are infinitely many Proth primes ([OEIS A080076](https://oeis.org/A080076)).

*Reference:* [Wikipedia: Proth prime](https://en.wikipedia.org/wiki/Proth_prime)
-/
@[category research open, AMS 11]
theorem infinitely_many_proth_primes : {N : ℕ | IsProthPrime N}.Infinite := by
  sorry

/--
There are infinitely many integers $n \ge 2$ such that $3 \cdot 2^n + 1$ is a Proth prime.

Primes of the form $3 \cdot 2^n + 1$ are also called *Thabit primes of the second kind*
([Wikipedia: Thabit number](https://en.wikipedia.org/wiki/Thabit_number)). Their exponents are
listed in [OEIS A002253](https://oeis.org/A002253), which also includes $n = 1$ ($3 \cdot 2^1 + 1 =
7$ is prime, whereas $n \ge 2$ ensures $3 < 2^n$).
-/
@[category research open, AMS 11]
theorem infinitely_many_proth_primes_multiplier_three :
    {n : ℕ | 2 ≤ n ∧ (3 * 2 ^ n + 1).Prime}.Infinite := by
  sorry

end ProthPrime
