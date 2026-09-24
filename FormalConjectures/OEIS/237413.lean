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

import FormalConjecturesUtil

/-!
# Ways to write $n = k + m$ with $p_k^2 - 2$, $p_m^2 - 2$, and $p_{p_m}^2 - 2$ all prime

Let $p_j$ denote the $j$-th prime number. The sequence $a(n)$ counts the number of ways to write
$n = k + m$ with $k > 0$ and $m > 0$ such that $p_k^2 - 2$, $p_m^2 - 2$, and $p_{p_m}^2 - 2$ are all
prime.

*References:*
- [A237413](https://oeis.org/A237413)
-/

namespace OeisA237413

/-- $a(n)$ is the number of ways to write $n = k + m$ with $k > 0$ and $m > 0$ such that
$p_k^2 - 2$, $p_m^2 - 2$, and $p_{p_m}^2 - 2$ are all prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Ico 1 n,
    if (Nat.nth Nat.Prime (k - 1) ^ 2 - 2).Prime ∧
       (Nat.nth Nat.Prime (n - k - 1) ^ 2 - 2).Prime ∧
       (Nat.nth Nat.Prime (Nat.nth Nat.Prime (n - k - 1) - 1) ^ 2 - 2).Prime then 1 else 0

private def nthPrimeSmall : ℕ → ℕ
  | 0 => 2
  | 1 => 3
  | 2 => 5
  | 3 => 7
  | 4 => 11
  | 5 => 13
  | 6 => 17
  | _ => 0

@[category API, AMS 11]
private lemma nth_prime_eq_small (k : ℕ) (hk : k ≤ 6) :
    Nat.nth Nat.Prime k = nthPrimeSmall k := by
  interval_cases k
  · exact Nat.nth_prime_zero_eq_two
  · exact Nat.nth_prime_one_eq_three
  · exact Nat.nth_prime_two_eq_five
  · exact Nat.nth_prime_three_eq_seven
  · exact Nat.nth_prime_four_eq_eleven
  · exact (13).nth_count (by decide : (13).Prime)
  · exact (17).nth_count (by decide : (17).Prime)

@[category API, AMS 11]
private lemma a_eq_small (n : ℕ) (hn : n ≤ 5) :
    a n = ∑ k ∈ Finset.Ico 1 n,
      if (nthPrimeSmall (k - 1) ^ 2 - 2).Prime ∧
         (nthPrimeSmall (n - k - 1) ^ 2 - 2).Prime ∧
         (nthPrimeSmall (nthPrimeSmall (n - k - 1) - 1) ^ 2 - 2).Prime then 1 else 0 := by
  unfold a
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_Ico] at hk
  have hk1 : k - 1 ≤ 6 := by omega
  have hm1 : n - k - 1 ≤ 6 := by omega
  have hm_small : nthPrimeSmall (n - k - 1) - 1 ≤ 6 := by
    have h4 : n - k - 1 ≤ 3 := by omega
    interval_cases (n - k - 1) <;> decide
  rw [nth_prime_eq_small (k - 1) hk1, nth_prime_eq_small (n - k - 1) hm1,
    nth_prime_eq_small (nthPrimeSmall (n - k - 1) - 1) hm_small]

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by
  rw [a_eq_small 1 (by decide)]
  decide +native

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  rw [a_eq_small 2 (by decide)]
  decide +native

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by
  rw [a_eq_small 3 (by decide)]
  decide +native

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 2 := by
  rw [a_eq_small 4 (by decide)]
  decide +native

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 2 := by
  rw [a_eq_small 5 (by decide)]
  decide +native

/--
Conjecture: $a(n) > 0$ for all $n > 1$.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 1 < n) : 0 < a n := by
  sorry

end OeisA237413
