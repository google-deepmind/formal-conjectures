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
# Smallest $k \ge 1$ such that the concatenation of $k$ threes and $\text{prime}(n)$ is prime

Let $b_k = 3 \dots 3$ consist of $k \ge 1$ threes in base $10$. The sequence $a(n)$ is the smallest
$k \ge 1$ such that the decimal concatenation of $b_k$ and $\text{prime}(n)$ is prime, or
$a(n) = 0$ if no such prime exists.

*References:*
- [A242775](https://oeis.org/A242775)
-/

@[expose] public section

namespace OeisA242775

/-- The number formed by concatenating $k$ threes with $p$ in base $10$. -/
def concatThrees (k p : ℕ) : ℕ :=
  ((10 ^ k - 1) / 3) * (10 ^ max 1 (Nat.digits 10 p).length) + p

@[category API, AMS 11]
private lemma ten_pow_sub_one_div_three_ge_three {k : ℕ} (hk : 0 < k) :
    3 ≤ (10 ^ k - 1) / 3 := by
  have : 10 ^ 1 ≤ 10 ^ k := Nat.pow_le_pow_right (by decide) hk
  omega

@[category API, AMS 11]
private lemma three_dvd_ten_pow_sub_one_div_three (k : ℕ) :
    3 ∣ (10 ^ k - 1) / 3 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have : 1 ≤ 10 ^ k := Nat.one_le_pow k 10 (by decide)
    have h2 : (10 ^ (k + 1) - 1) / 3 = 3 * 10 ^ k + (10 ^ k - 1) / 3 := by
      omega
    rw [h2]
    exact dvd_add (dvd_mul_right 3 _) ih

/-- Smallest $k \ge 1$ such that the concatenation of $k$ threes and $\text{prime}(n)$ is prime,
or $0$ if no such prime exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else sInf {k : ℕ | 0 < k ∧ Nat.Prime (concatThrees k (Nat.nth Nat.Prime (n - 1)))}

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by
  dsimp [a]
  rw [Nat.nth_prime_zero_eq_two]
  suffices {k : ℕ | 0 < k ∧ (concatThrees k 2).Prime} = ∅ by simp [this]
  refine Set.eq_empty_of_forall_notMem fun k ⟨hk, hp⟩ => ?_
  have hval : concatThrees k 2 = ((10 ^ k - 1) / 3) * 10 + 2 := rfl
  have hdvd : 2 ∣ concatThrees k 2 := by
    rw [hval]
    exact dvd_add (dvd_mul_of_dvd_right (by decide) _) (dvd_refl 2)
  have hgt : 2 < concatThrees k 2 := by
    have := ten_pow_sub_one_div_three_ge_three hk
    omega
  rcases hp.eq_one_or_self_of_dvd 2 hdvd with h | h <;> omega

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by
  dsimp [a]
  rw [Nat.nth_prime_one_eq_three]
  suffices {k : ℕ | 0 < k ∧ (concatThrees k 3).Prime} = ∅ by simp [this]
  refine Set.eq_empty_of_forall_notMem fun k ⟨hk, hp⟩ => ?_
  have hval : concatThrees k 3 = ((10 ^ k - 1) / 3) * 10 + 3 := rfl
  have hdvd : 3 ∣ concatThrees k 3 := by
    rw [hval]
    exact dvd_add (dvd_mul_of_dvd_left (three_dvd_ten_pow_sub_one_div_three k) _) (dvd_refl 3)
  have hgt : 3 < concatThrees k 3 := by
    have := ten_pow_sub_one_div_three_ge_three hk
    omega
  rcases hp.eq_one_or_self_of_dvd 3 hdvd with h | h <;> omega

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by
  dsimp [a]
  rw [Nat.nth_prime_two_eq_five]
  suffices {k : ℕ | 0 < k ∧ (concatThrees k 5).Prime} = ∅ by simp [this]
  refine Set.eq_empty_of_forall_notMem fun k ⟨hk, hp⟩ => ?_
  have hval : concatThrees k 5 = ((10 ^ k - 1) / 3) * 10 + 5 := rfl
  have hdvd : 5 ∣ concatThrees k 5 := by
    rw [hval]
    exact dvd_add (dvd_mul_of_dvd_right (by decide) _) (dvd_refl 5)
  have hgt : 5 < concatThrees k 5 := by
    have := ten_pow_sub_one_div_three_ge_three hk
    omega
  rcases hp.eq_one_or_self_of_dvd 5 hdvd with h | h <;> omega

@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by
  dsimp [a]
  rw [Nat.nth_prime_three_eq_seven]
  exact IsLeast.csInf_eq (by decide)

@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by
  dsimp [a]
  rw [Nat.nth_prime_four_eq_eleven]
  exact IsLeast.csInf_eq (by decide +kernel)

@[category test, AMS 11]
theorem a_6 : a 6 = 1 := by
  dsimp [a]
  rw [Nat.nth_prime_five_eq_thirteen]
  exact IsLeast.csInf_eq (by decide +kernel)

@[category test, AMS 11]
theorem a_7 : a 7 = 1 := by
  dsimp [a]
  rw [Nat.nth_prime_six_eq_seventeen]
  exact IsLeast.csInf_eq (by decide +kernel)

set_option maxRecDepth 10000 in
@[category test, AMS 11]
theorem a_8 : a 8 = 2 := by
  dsimp [a]
  rw [Nat.nth_prime_seven_eq_nineteen]
  exact IsLeast.csInf_eq (by decide +kernel)

/--
Conjecture: For $n \ge 4$, $a(n) > 0$.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 4 ≤ n) : 0 < a n := by
  sorry

end OeisA242775
