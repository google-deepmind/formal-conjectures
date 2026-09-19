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
# Ordered ways to write $2n = p + q$ with $p, q$ and $p_{p+2} + 2$ all prime

Let $p_k$ denote the $k$-th prime number. The sequence $a(n)$ counts the number of ordered ways to
write $2n = p + q$ with $p, q$, and $p_{p+2} + 2$ all prime.

*References:*
- [A236566](https://oeis.org/A236566)
-/

namespace OeisA236566

/-- $a(n)$ is the number of ordered ways to write $2n = p + q$ with $p, q$ and
$\operatorname{prime}(p + 2) + 2$ all prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  ∑ p ∈ Finset.range (2 * n),
    if p.Prime ∧ (2 * n - p).Prime ∧ (Nat.nth Nat.Prime (p + 1) + 2).Prime then 1 else 0

private def nthPrimeSmall : ℕ → ℕ
  | 0 => 2
  | 1 => 3
  | 2 => 5
  | 3 => 7
  | 4 => 11
  | 5 => 13
  | 6 => 17
  | 7 => 19
  | 8 => 23
  | 9 => 29
  | 10 => 31
  | _ => 0

@[category API, AMS 11]
private lemma nth_prime_eq_small (k : ℕ) (hk : k ≤ 10) :
    Nat.nth Nat.Prime k = nthPrimeSmall k := by
  interval_cases k
  · exact Nat.nth_prime_zero_eq_two
  · exact Nat.nth_prime_one_eq_three
  · exact Nat.nth_prime_two_eq_five
  · exact Nat.nth_prime_three_eq_seven
  · exact Nat.nth_prime_four_eq_eleven
  · exact (13).nth_count (by decide : (13).Prime)
  · exact (17).nth_count (by decide : (17).Prime)
  · exact (19).nth_count (by decide : (19).Prime)
  · exact (23).nth_count (by decide : (23).Prime)
  · exact (29).nth_count (by decide : (29).Prime)
  · exact (31).nth_count (by decide : (31).Prime)

@[category API, AMS 11]
private lemma a_eq_small (n : ℕ) (hn : n ≤ 5) :
    a n = ∑ p ∈ Finset.range (2 * n),
      if p.Prime ∧ (2 * n - p).Prime ∧ (nthPrimeSmall (p + 1) + 2).Prime then 1 else 0 := by
  unfold a
  apply Finset.sum_congr rfl
  intro p hp
  have hp1 : p + 1 ≤ 10 := by
    rw [Finset.mem_range] at hp
    omega
  rw [nth_prime_eq_small (p + 1) hp1]

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by
  rw [a_eq_small 1 (by decide)]
  decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by
  rw [a_eq_small 2 (by decide)]
  decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by
  rw [a_eq_small 3 (by decide)]
  decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 2 := by
  rw [a_eq_small 4 (by decide)]
  decide

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 2 := by
  rw [a_eq_small 5 (by decide)]
  decide

/--
Conjecture: (i) $a(n) > 0$ for all $n > 2$.
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : 2 < n) : 0 < a n := by
  sorry

/--
Conjecture: (ii) If $n > 30$, then $2n + 1$ can be written as $2p + q$ with $p$, $q$ and
$\operatorname{prime}(p + 2) + 2$ all prime.
-/
@[category research open, AMS 11]
theorem conjecture2 (n : ℕ) (hn : 30 < n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ (Nat.nth Nat.Prime (p + 1) + 2).Prime ∧
      2 * n + 1 = 2 * p + q := by
  sorry

end OeisA236566
