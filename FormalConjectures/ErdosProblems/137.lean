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
# Erdős Problem 137

*References:*
- [erdosproblems.com/137](https://www.erdosproblems.com/137)
-/

@[expose] public section

namespace Erdos137

/--
We say that $N$ is powerful if whenever $p\mid N$ we also have $p^2\mid N$.

Let $k\geq 3$. Can the product of any $k$ consecutive positive integers ever be powerful?
-/
@[category research open, question, AMS 11]
theorem erdos_137 : ∃ k ≥ 3, ∃ n, (∏ x ∈ Finset.Ioc n (n + k), x).Powerful := by
  sorry

/-- A positive integer is powerful if and only if no prime occurs to exponent $1$. -/
@[category API, AMS 11]
private theorem powerful_iff_factorization_ne_one {n : ℕ} (hn : n ≠ 0) :
    n.Powerful ↔ ∀ p : ℕ, p.Prime → n.factorization p ≠ 1 := by
  simp only [Nat.Full, Nat.mem_primeFactors]
  constructor
  · intro h p hp h1
    have hd := (hp.dvd_iff_one_le_factorization hn).mpr (by omega)
    have h2 := (hp.pow_dvd_iff_le_factorization hn).mp (h p ⟨hp, hd, hn⟩)
    omega
  · intro h p hp
    have h1 := (hp.1.dvd_iff_one_le_factorization hn).mp hp.2.1
    have h2 := h p hp.1
    exact (hp.1.pow_dvd_iff_le_factorization hn).mpr (by omega)

/-- The odd part of a positive integer is powerful if and only if no odd prime occurs to
exponent $1$ in the integer. -/
@[category API, AMS 11]
private theorem odd_part_powerful_iff {n : ℕ} (hn : n ≠ 0) :
    (ordCompl[2] n).Powerful ↔ ∀ p : ℕ, p.Prime → p ≠ 2 → n.factorization p ≠ 1 := by
  rw [powerful_iff_factorization_ne_one (Nat.ordCompl_pos 2 hn).ne']
  simp only [Nat.factorization_ordCompl]
  constructor
  · intro h p hp hp2
    simpa [Finsupp.erase_ne hp2] using h p hp
  · intro h p hp
    by_cases hp2 : p = 2
    · simp [hp2]
    · simpa [Finsupp.erase_ne hp2] using h p hp hp2

/-- The product of three consecutive integers is divisible by $4$ exactly when the middle term
is odd or divisible by $4$. -/
@[category API, AMS 11]
private theorem triple_four_dvd_iff (n : ℕ) :
    4 ∣ n * (n + 1) * (n + 2) ↔ (n + 1) % 4 ≠ 2 := by
  have h1 : (n + 1) % 4 = (n % 4 + 1) % 4 := by omega
  have h2 : (n + 2) % 4 = (n % 4 + 2) % 4 := by omega
  rw [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod (n * (n + 1)), Nat.mul_mod n, h1, h2]
  have hlt : n % 4 < 4 := Nat.mod_lt _ (by decide)
  interval_cases n % 4 <;> decide

/-- A product of three consecutive positive integers is powerful exactly when each odd part
is powerful and the middle term is odd or divisible by $4$. An odd prime can divide only one
of the three terms, while the factors of $2$ from the two endpoints can combine. -/
@[category API, AMS 11]
theorem powerful_triple_iff {n : ℕ} (hn : 0 < n) :
    (n * (n + 1) * (n + 2)).Powerful ↔
      (ordCompl[2] n).Powerful ∧ (ordCompl[2] (n + 1)).Powerful ∧
      (ordCompl[2] (n + 2)).Powerful ∧ (n + 1) % 4 ≠ 2 := by
  have h01 : n * (n + 1) ≠ 0 := by positivity
  have hprod : n * (n + 1) * (n + 2) ≠ 0 := by positivity
  have heven : 2 ∣ n * (n + 1) * (n + 2) := by
    have h : 2 ∣ n ∨ 2 ∣ n + 1 := by omega
    exact dvd_mul_of_dvd_left (Nat.prime_two.dvd_mul.mpr h) _
  have h2 : (n * (n + 1) * (n + 2)).factorization 2 ≠ 1 ↔ (n + 1) % 4 ≠ 2 := by
    have hpos := (Nat.prime_two.dvd_iff_one_le_factorization hprod).mp heven
    rw [← triple_four_dvd_iff, ← show (2 : ℕ) ^ 2 = 4 by decide,
      Nat.prime_two.pow_dvd_iff_le_factorization hprod]
    omega
  rw [powerful_iff_factorization_ne_one hprod, odd_part_powerful_iff hn.ne',
    odd_part_powerful_iff (by omega : n + 1 ≠ 0), odd_part_powerful_iff (by omega : n + 2 ≠ 0),
    ← h2]
  have hodd (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
      (n * (n + 1) * (n + 2)).factorization p ≠ 1 ↔
        n.factorization p ≠ 1 ∧ (n + 1).factorization p ≠ 1 ∧ (n + 2).factorization p ≠ 1 := by
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have aux (a b : ℕ) (hab : a < b) (hdiff : b - a ≤ 2) (ha : p ∣ a) (hb : p ∣ b) :
        False := by
      have := Nat.le_of_dvd (by omega : 0 < b - a) (Nat.dvd_sub hb ha)
      omega
    rw [Nat.factorization_mul h01 (by omega), Nat.factorization_mul hn.ne' (by omega)]
    simp only [Finsupp.add_apply]
    by_cases ha : p ∣ n
    · rw [Nat.factorization_eq_zero_of_not_dvd (fun hb ↦ aux n (n + 1) (by omega) (by omega) ha hb),
        Nat.factorization_eq_zero_of_not_dvd (fun hb ↦ aux n (n + 2) (by omega) (by omega) ha hb)]
      simp
    · rw [Nat.factorization_eq_zero_of_not_dvd ha]
      by_cases hb : p ∣ n + 1
      · rw [Nat.factorization_eq_zero_of_not_dvd (fun hc ↦
          aux (n + 1) (n + 2) (by omega) (by omega) hb hc)]
        simp
      · simp [Nat.factorization_eq_zero_of_not_dvd hb]
  constructor
  · intro h
    exact ⟨fun p hp hp2 ↦ ((hodd p hp hp2).mp (h p hp)).1,
      fun p hp hp2 ↦ ((hodd p hp hp2).mp (h p hp)).2.1,
      fun p hp hp2 ↦ ((hodd p hp hp2).mp (h p hp)).2.2, h 2 Nat.prime_two⟩
  · rintro ⟨ha, hb, hc, ht⟩ p hp
    obtain rfl | hp2 := eq_or_ne p 2
    · exact ht
    · exact (hodd p hp hp2).mpr ⟨ha p hp hp2, hb p hp hp2, hc p hp hp2⟩

/--
Let $k\geq 2$. Erdős and Selfridge [ES75] proved that the product of any $k$ consecutive
integers $N$ cannot be a perfect power.

[ES75] P. Erdös, J. L. Selfridge, "The product of consecutive integers is never a power",
  Illinois J. Math. 19(2): 292-301, 1975
-/
@[category research solved, AMS 11]
theorem erdos_137.variants.perfect_power (k : ℕ) (hk : k ≥ 2) (n : ℕ) (x l : ℕ) (hl : 2 ≤ l) :
    (∏ x ∈ Finset.Ioc n (n + k), x) ≠ x ^ l := by
  sorry

/--
Erdős [Er82c] conjectures that, if $k$ is fixed, then for all $n$ sufficiently large and all
positive integers $m$, there must be at least $k$ distinct primes $p$ such that
$p\mid m(m+1)\cdots (m+n)$ and yet $p^2$ does not divide the right hand side.

[Er82c] Erdős, Paul, "Miscellaneous problems in number theory". Congr. Numer. (1982), 25-45.,
-/
@[category research open, AMS 11]
theorem erdos_137.variants.multiple_powerful_factors (k : ℕ) : ∀ᶠ n in Filter.atTop,
    ∀ (m : ℕ) (hm : 0 < m),
    letI N := ∏ x ∈ Finset.Ioc m (m + n), x
    ∃ P : Finset ℕ, P.card = k ∧ ∀ p ∈ P, p.Prime ∧
    p ∣ N ∧ ¬ p ^ 2 ∣ N := by
  sorry

end Erdos137
