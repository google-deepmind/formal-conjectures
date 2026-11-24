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
# Multiply Perfect Numbers

Given $k \in \mathbb{N}$, an integer $n \ge 1$ is *$k$-perfect* (`Nat.IsPerfectFor n 1 k`) if its
divisor sum satisfies $\sigma_1(n) = k n$, and *multiply perfect* if it is $k$-perfect for some
$k \in \mathbb{N}$. Ordinary perfect numbers correspond to $k = 2$ (see
`FormalConjectures.Wikipedia.PerfectNumbers`), while $k = 3$ gives the *triperfect* numbers
(`OEIS A005820`), of which six examples are known:
$120, 672, 523776, 459818240, 1476304896, 51001180160$. Whether an odd multiply perfect integer
exceeding $1$ exists, and whether these six values exhaust all triperfect numbers, remain open
(for general $k \ge 3$ finiteness, see `FormalConjectures.ErdosProblems.«1053»`).

*References:*
- [Wikipedia: Multiply perfect number](https://en.wikipedia.org/wiki/Multiply_perfect_number)
- [OEIS A005820](https://oeis.org/A005820)
- [Ki87] M. Kishore, *Odd triperfect numbers are divisible by twelve distinct prime factors*,
  J. Austral. Math. Soc. Ser. A **42** (1987), no. 2, 173–182.
  https://doi.org/10.1017/S1446788700028184
-/

@[expose] public section

namespace MultiplyPerfectNumber

open scoped ArithmeticFunction.sigma

/-- The six known $3$-perfect (triperfect) numbers (`OEIS A005820`). -/
def knownTriperfectNumbers : Finset ℕ :=
  {120, 672, 523776, 459818240, 1476304896, 51001180160}

/-- $28$ is a $2$-perfect (ordinary perfect) number ($\sigma_1(28) = 56$). -/
@[category test, AMS 11]
theorem isPerfectFor_28 : Nat.IsPerfectFor 28 1 2 := by
  unfold Nat.IsPerfectFor
  decide

/-- $120$ is the smallest $3$-perfect number ($\sigma_1(120) = 360$). -/
@[category test, AMS 11]
theorem isPerfectFor_120 : Nat.IsPerfectFor 120 1 3 := by
  unfold Nat.IsPerfectFor
  decide

/-- $672$ is triperfect ($\sigma_1(672) = 2016 = 3 \cdot 672$). -/
@[category test, AMS 11]
theorem isPerfectFor_672 : Nat.IsPerfectFor 672 1 3 := by
  unfold Nat.IsPerfectFor
  decide

/-- Every element of `knownTriperfectNumbers` satisfies $\sigma_1(n) = 3 n$. -/
@[category test, AMS 11]
theorem isPerfectFor_of_mem_knownTriperfectNumbers :
    ∀ n ∈ knownTriperfectNumbers, Nat.IsPerfectFor n 1 3 := by
  have hpp : ∀ p e : ℕ, p.Prime → σ 1 (p ^ e) = ∑ j ∈ Finset.range (e + 1), p ^ j :=
    fun _ e hp ↦ ArithmeticFunction.sigma_one_apply_prime_pow (i := e) hp
  have hp1 : ∀ p : ℕ, p.Prime → σ 1 p = p + 1 := fun p hp ↦ by
    have h1 := hpp p 1 hp
    simp only [pow_one, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero] at h1
    omega
  have hmul : ∀ a b : ℕ, a.Coprime b → σ 1 (a * b) = σ 1 a * σ 1 b :=
    fun _ _ h ↦ ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h
  intro n hn
  simp only [knownTriperfectNumbers, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
  · exact isPerfectFor_120
  · exact isPerfectFor_672
  · refine ⟨by norm_num, ?_⟩
    change σ 1 523776 = 3 * 523776
    have h2 : σ 1 (2 ^ 9) = 1023 := by rw [hpp 2 9 (by decide)]; decide
    rw [show (523776 : ℕ) = 2 ^ 9 * (3 * (11 * 31)) by norm_num,
      hmul _ _ (by decide), hmul _ _ (by decide), hmul _ _ (by decide),
      h2, hp1 3 (by decide), hp1 11 (by decide), hp1 31 (by decide)]
    norm_num
  · refine ⟨by norm_num, ?_⟩
    change σ 1 459818240 = 3 * 459818240
    have h2 : σ 1 (2 ^ 8) = 511 := by rw [hpp 2 8 (by decide)]; decide
    rw [show (459818240 : ℕ) = 2 ^ 8 * (5 * (7 * (19 * (37 * 73)))) by norm_num,
      hmul _ _ (by decide), hmul _ _ (by decide), hmul _ _ (by decide),
      hmul _ _ (by decide), hmul _ _ (by decide), h2, hp1 5 (by decide),
      hp1 7 (by decide), hp1 19 (by decide), hp1 37 (by decide), hp1 73 (by decide)]
    norm_num
  · refine ⟨by norm_num, ?_⟩
    change σ 1 1476304896 = 3 * 1476304896
    have h2 : σ 1 (2 ^ 13) = 16383 := by rw [hpp 2 13 (by decide)]; decide
    rw [show (1476304896 : ℕ) = 2 ^ 13 * (3 * (11 * (43 * 127))) by norm_num,
      hmul _ _ (by decide), hmul _ _ (by decide), hmul _ _ (by decide),
      hmul _ _ (by decide), h2, hp1 3 (by decide), hp1 11 (by decide),
      hp1 43 (by decide), hp1 127 (by decide)]
    norm_num
  · refine ⟨by norm_num, ?_⟩
    change σ 1 51001180160 = 3 * 51001180160
    have h2 : σ 1 (2 ^ 14) = 32767 := by rw [hpp 2 14 (by decide)]; decide
    rw [show (51001180160 : ℕ) = 2 ^ 14 * (5 * (7 * (19 * (31 * 151)))) by norm_num,
      hmul _ _ (by decide), hmul _ _ (by decide), hmul _ _ (by decide),
      hmul _ _ (by decide), hmul _ _ (by decide), h2, hp1 5 (by decide),
      hp1 7 (by decide), hp1 19 (by decide), hp1 31 (by decide), hp1 151 (by decide)]
    norm_num

/-- The set `knownTriperfectNumbers` contains $6$ distinct integers. -/
@[category test, AMS 11]
theorem card_knownTriperfectNumbers : knownTriperfectNumbers.card = 6 := by
  decide

/-- The only $1$-perfect positive integer is $n = 1$. -/
@[category API, AMS 11]
theorem isPerfectFor_one_one_iff {n : ℕ} : Nat.IsPerfectFor n 1 1 ↔ n = 1 := by
  constructor
  · rintro ⟨hn, hsig⟩
    simp only [Function.iterate_one, one_mul, ArithmeticFunction.sigma_one_apply] at hsig
    by_contra hne
    have hsub : ({1, n} : Finset ℕ) ⊆ n.divisors := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · exact Nat.one_mem_divisors.mpr hn.ne'
      · rw [Finset.mem_singleton.mp hx']
        exact Nat.mem_divisors_self n hn.ne'
    have hle : ∑ d ∈ ({1, n} : Finset ℕ), d ≤ ∑ d ∈ n.divisors, d :=
      Finset.sum_le_sum_of_subset hsub
    rw [Finset.sum_pair (Ne.symm hne), hsig] at hle
    omega
  · rintro rfl
    unfold Nat.IsPerfectFor
    decide

/-- Multiplying a $p$-perfect integer $n$ by a prime $p \nmid n$ yields a $(p + 1)$-perfect
integer. -/
@[category textbook, AMS 11]
theorem isPerfectFor_prime_mul {p n : ℕ} (hp : p.Prime) (hn : Nat.IsPerfectFor n 1 p)
    (hndvd : ¬ p ∣ n) : Nat.IsPerfectFor (p * n) 1 (p + 1) := by
  rcases hn with ⟨hnpos, hsig⟩
  change σ 1 n = p * n at hsig
  refine ⟨mul_pos hp.pos hnpos, ?_⟩
  change σ 1 (p * n) = (p + 1) * (p * n)
  have hcop : p.Coprime n := hp.coprime_iff_not_dvd.mpr hndvd
  have hsig_p : σ 1 p = p + 1 := by
    have h1 := ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) hp
    simp only [pow_one, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero] at h1
    omega
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hsig_p, hsig]

/--
**Odd Multiply Perfect Number Question**: Does there exist an odd multiply perfect integer
$n > 1$?
-/
@[category research open, question, AMS 11]
theorem exists_odd_multiply_perfect_gt_one :
    ∃ n k : ℕ, 1 < n ∧ Odd n ∧ Nat.IsPerfectFor n 1 k := by
  sorry

/--
**Completeness of Known Triperfect Numbers**: The $3$-perfect numbers are precisely the six
elements of `knownTriperfectNumbers`.
-/
@[category research open, AMS 11]
theorem triperfect_numbers_eq :
    {n : ℕ | Nat.IsPerfectFor n 1 3} = (knownTriperfectNumbers : Set ℕ) := by
  sorry

/--
**Kishore's Bound on Odd Triperfect Numbers** [Ki87]: At least twelve distinct primes divide every
odd $3$-perfect integer.
-/
@[category research solved, AMS 11]
theorem kishore_odd_triperfect_prime_factors {n : ℕ} (hodd : Odd n)
    (htri : Nat.IsPerfectFor n 1 3) : 12 ≤ n.primeFactors.card := by
  sorry

end MultiplyPerfectNumber
