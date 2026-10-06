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
# Erdős Problem 365

*References:*
- [erdosproblems.com/365](https://www.erdosproblems.com/365)
- [Go70] Golomb, S. W., *Powerful numbers*. Amer. Math. Monthly (1970), 848-855.
- [Gu04] Guy, R. K., *Unsolved problems in number theory* (2004), Problem B16.
- [Wa76] Walker, D. T., *Consecutive integer pairs of powerful numbers and related
  Diophantine equations*. Fibonacci Quart. (1976), 111-116.
-/

@[expose] public section

namespace Erdos365

/-- Golomb's consecutive powerful pair $12167=23^3$ and $12168=2^3 3^2 13^2$.
Neither number is a square [Go70]. -/
@[category test, AMS 11]
theorem golomb_pair :
    Nat.Powerful 12167 ∧ Nat.Powerful 12168 ∧
      ¬ IsSquare (12167 : ℕ) ∧ ¬ IsSquare (12168 : ℕ) := by
  have hA : Nat.Powerful 12167 := by
    intro p hp
    obtain ⟨hp, hd, _⟩ := Nat.mem_primeFactors.mp hp
    have hpow : p ∣ (23 : ℕ) ^ 3 := by norm_num at hd ⊢; exact hd
    have heq : p = 23 := Nat.prime_eq_prime_of_dvd_pow hp (by norm_num) hpow
    subst p
    norm_num
  have hB : Nat.Powerful 12168 := by
    intro p hp
    obtain ⟨hp, hd, _⟩ := Nat.mem_primeFactors.mp hp
    have hprod : p ∣ (2 : ℕ) ^ 3 * 3 ^ 2 * 13 ^ 2 := by norm_num at hd ⊢; exact hd
    rcases hp.dvd_mul.mp hprod with hab | hc
    · rcases hp.dvd_mul.mp hab with ha | hb
      · have heq : p = 2 := Nat.prime_eq_prime_of_dvd_pow hp (by norm_num) ha
        subst p
        norm_num
      · have heq : p = 3 := Nat.prime_eq_prime_of_dvd_pow hp (by norm_num) hb
        subst p
        norm_num
    · have heq : p = 13 := Nat.prime_eq_prime_of_dvd_pow hp (by norm_num) hc
      subst p
      norm_num
  have hns : ∀ n : ℕ, 12100 < n → n < 12321 → ¬ IsSquare n := by
    intro n hlo hhi ⟨r, hr⟩
    have hrlo : 110 < r := by nlinarith
    have hrhi : r < 111 := by nlinarith
    omega
  exact ⟨hA, hB, hns _ (by norm_num) (by norm_num), hns _ (by norm_num) (by norm_num)⟩

/--
Do all pairs of consecutive powerful numbers $n$ and $n+1$ come from solutions to Pell
equations? In other words, must either $n$ or $n+1$ be a square?

The answer to the first question is no: Golomb [Go70] observed that both $12167=23^3$ and
$12168=2^3 3^2 13^2$ are powerful.

We require $n>0$ since `Nat.Powerful` also includes $0$.
-/
@[category research solved, AMS 11]
theorem erdos_365.parts.i : answer(False) ↔
    ∀ n : ℕ, 0 < n → Nat.Powerful n → Nat.Powerful (n + 1) →
      IsSquare n ∨ IsSquare (n + 1) := by
  constructor
  · intro h
    exact False.elim h
  · intro h
    obtain ⟨hA, hB, hnA, hnB⟩ := golomb_pair
    rcases h 12167 (by norm_num) hA hB with hs | hs
    · exact hnA hs
    · exact hnB hs

/-- Is the number of positive $n\leq x$ such that $n$ and $n+1$ are both powerful bounded
by $(\log x)^{O(1)}$? -/
@[category research open, AMS 11]
theorem erdos_365.parts.ii : answer(sorry) ↔
    ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∀ᶠ x : ℕ in Filter.atTop,
      ({n : ℕ | 0 < n ∧ n ≤ x ∧ Nat.Powerful n ∧ Nat.Powerful (n + 1)}.ncard : ℝ) ≤
        C * (Real.log x) ^ k := by
  sorry

end Erdos365
