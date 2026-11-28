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
# Determinants of 2 X 2 matrices of non-overlapping blocks of 4 consecutive primes

$a(n) = p_{4n-3}p_{4n} - p_{4n-2}p_{4n-1}$ where $p_k$ is the k-th prime number (1-indexed).

*References:*
- [A117027](https://oeis.org/A117027)
-/

@[expose] public section

namespace OeisA117027

open Nat Int Filter

/-- a n is the determinant of a 2x2 matrix of non-overlapping blocks of 4 consecutive primes. -/
noncomputable def a (n : ℕ) : ℤ :=
  if 0 < n then
    let k := 4 * n
    let pPrime (i : ℕ) : ℤ := (Nat.nth Nat.Prime i : ℤ)

    let p₁ := pPrime (k - 4) -- p_{4n-4} in 0-indexed Mathlib
    let p₂ := pPrime (k - 1) -- p_{4n-1} in 0-indexed Mathlib
    let p₃ := pPrime (k - 3) -- p_{4n-3} in 0-indexed Mathlib
    let p₄ := pPrime (k - 2) -- p_{4n-2} in 0-indexed Mathlib

    p₁ * p₂ - p₃ * p₄
  else
    0

@[category API, AMS 11]
lemma nth_prime_five : Nat.nth Nat.Prime 5 = 13 := by
  have h1 : (13).Prime := by decide
  exact Nat.nth_count h1

@[category API, AMS 11]
lemma nth_prime_six : Nat.nth Nat.Prime 6 = 17 := by
  have h1 : (17).Prime := by decide
  exact Nat.nth_count h1

@[category API, AMS 11]
lemma nth_prime_seven : Nat.nth Nat.Prime 7 = 19 := by
  have h1 : (19).Prime := by decide
  exact Nat.nth_count h1

@[category API, AMS 11]
lemma nth_prime_eight : Nat.nth Nat.Prime 8 = 23 := by
  have h1 : (23).Prime := by decide
  exact Nat.nth_count h1

@[category API, AMS 11]
lemma nth_prime_nine : Nat.nth Nat.Prime 9 = 29 := by
  have h1 : (29).Prime := by decide
  exact Nat.nth_count h1

@[category API, AMS 11]
lemma nth_prime_ten : Nat.nth Nat.Prime 10 = 31 := by
  have h1 : (31).Prime := by decide
  exact Nat.nth_count h1

@[category API, AMS 11]
lemma nth_prime_eleven : Nat.nth Nat.Prime 11 = 37 := by
  have h1 : (37).Prime := by decide
  exact Nat.nth_count h1

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by
  rfl

@[category test, AMS 11]
theorem a_1 : a 1 = -1 := by
  dsimp [a]
  rw [Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five,
      Nat.nth_prime_three_eq_seven]
  norm_num

@[category test, AMS 11]
theorem a_2 : a 2 = -12 := by
  dsimp [a]
  rw [Nat.nth_prime_four_eq_eleven, nth_prime_seven, nth_prime_five, nth_prime_six]
  norm_num

@[category test, AMS 11]
theorem a_3 : a 3 = -48 := by
  dsimp [a]
  rw [nth_prime_eight, nth_prime_eleven, nth_prime_nine, nth_prime_ten]
  norm_num

/-- Write a block as four primes starting at $p$ with successive gaps $g_1,g_2,g_3$.
Its determinant is $p(g_3-g_1)-g_1(g_1+g_2)$. -/
@[category API, AMS 11]
theorem a_succ_eq_prime_gaps (n : ℕ) :
    let p (i : ℕ) : ℤ := Nat.nth Nat.Prime (4 * n + i)
    let g₁ := p 1 - p 0
    let g₂ := p 2 - p 1
    let g₃ := p 3 - p 2
    a (n + 1) = p 0 * (g₃ - g₁) - g₁ * (g₁ + g₂) := by
  simp [a, Nat.mul_add, Nat.add_sub_assoc]
  ring

/-- The largest prime of a block divides neither middle prime, so its determinant is nonzero. -/
@[category API, AMS 11]
theorem a_ne_zero {n : ℕ} (hn : 0 < n) : a n ≠ 0 := by
  simp only [a, if_pos hn, ne_eq, sub_eq_zero]
  intro h
  let p := Nat.nth Nat.Prime
  have heq : p (4 * n - 4) * p (4 * n - 1) = p (4 * n - 3) * p (4 * n - 2) := by
    exact_mod_cast h
  have hd : p (4 * n - 1) ∣ p (4 * n - 3) * p (4 * n - 2) := heq ▸ dvd_mul_left _ _
  have small (i : ℕ) (hi : i < 4 * n - 1) : ¬ p (4 * n - 1) ∣ p i :=
    Nat.not_dvd_of_pos_of_lt (Nat.prime_nth_prime i).pos
      (Nat.nth_strictMono Nat.infinite_setOfPred_prime hi)
  exact ((Nat.prime_nth_prime _).dvd_mul.mp hd).elim (small _ (by omega)) (small _ (by omega))

/-- The count of positive terms among $a(1)$, ..., $a(N)$. -/
noncomputable def positiveCount (N : ℕ) : ℕ :=
  (List.range N).countP (fun n => 0 < a (n + 1))

/-- The count of negative terms among $a(1)$, ..., $a(N)$. -/
noncomputable def negativeCount (N : ℕ) : ℕ :=
  (List.range N).countP (fun n => a (n + 1) < 0)

/-- Each of the first $N$ determinants contributes to exactly one of the two counts. -/
@[category API, AMS 11]
theorem positiveCount_add_negativeCount (N : ℕ) : positiveCount N + negativeCount N = N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rcases lt_or_gt_of_ne (a_ne_zero (Nat.succ_pos N)) with h | h <;>
      simp [positiveCount, negativeCount, List.range_succ, h, h.asymm] at * <;> omega

/-- The sequence of ratios $P(N)/Neg(N)$ as a sequence of real numbers. -/
noncomputable def ratioSeq (N : ℕ) : ℝ :=
  if negativeCount N = 0 then
    0
  else
    (positiveCount N : ℝ) / (negativeCount N : ℝ)

/-- The OEIS entry suggests a limiting ratio close to $0.87$. This statement interprets
closeness as membership in the interval $(0.8,0.9)$. -/
@[category research open, AMS 11]
theorem conjecture :
  ∃ L : ℝ, Tendsto ratioSeq atTop (nhds L) ∧ 0.8 < L ∧ L < 0.9 :=
by sorry

/-- The OEIS entry also reports a consistent excess of negative terms.
Does every nonempty initial segment contain more negative terms than positive terms? -/
@[category research open, question, AMS 11]
theorem conjecture.variants.negative_majority : ∀ N > 0, positiveCount N < negativeCount N := by
  sorry

/-- A limiting ratio below one gives a negative majority in every sufficiently long prefix. -/
@[category API, AMS 11]
theorem eventually_negative_majority_of_tendsto {L : ℝ} (hL : L < 1)
    (h : Tendsto ratioSeq atTop (nhds L)) : ∀ᶠ N in atTop, positiveCount N < negativeCount N := by
  filter_upwards [h.eventually_lt_const hL, eventually_gt_atTop (0 : ℕ)] with N hr hN
  have hneg : 0 < negativeCount N := by
    exact List.countP_pos_iff.mpr ⟨0, List.mem_range.mpr hN, by norm_num [a_1]⟩
  rw [ratioSeq, if_neg hneg.ne', div_lt_one (by exact_mod_cast hneg)] at hr
  exact_mod_cast hr

end OeisA117027
