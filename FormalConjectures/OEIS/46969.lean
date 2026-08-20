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
# Denominators of coefficients in Stirling's expansion for $\log(\Gamma(z))$

The $n$-th term is the denominator of $\frac{B_{2n}}{2n(2n-1)}$ where $B_{2n}$ is the $2n$-th
Bernoulli number.

*References:*
- [A046969](https://oeis.org/A046969)-/

namespace OeisA46969

/-- Denominators of coefficients in Stirling's expansion for $\log(\Gamma(z))$. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let m := 2 * n
    let k := m * (m - 1)
    (bernoulli m / (k : ℚ)).den

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 12 := by
  dsimp [a]
  rw [bernoulli_two]
  norm_num

@[category test, AMS 11]
theorem a_2 : a 2 = 360 := by
  dsimp [a]
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_four]
  norm_num

@[category API, AMS 11]
lemma bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  have hchoose2 : Nat.choose 6 2 = 15 := by decide
  have hchoose3 : Nat.choose 6 3 = 20 := by decide
  have hchoose4 : Nat.choose 6 4 = 15 := by decide
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by decide)
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_two, bernoulli'_three,
    bernoulli'_four, h5, hchoose2, hchoose3, hchoose4]

@[category test, AMS 11]
theorem a_3 : a 3 = 1260 := by
  dsimp [a]
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_six]
  norm_num

@[category API, AMS 11]
lemma bernoulli'_eight : bernoulli' 8 = -1 / 30 := by
  have hchoose2 : Nat.choose 8 2 = 28 := by decide
  have hchoose3 : Nat.choose 8 3 = 56 := by decide
  have hchoose4 : Nat.choose 8 4 = 70 := by decide
  have hchoose5 : Nat.choose 8 5 = 56 := by decide
  have hchoose6 : Nat.choose 8 6 = 28 := by decide
  have h3 : bernoulli' 3 = 0 := bernoulli'_three
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by decide)
  have h7 : bernoulli' 7 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by decide)
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_two, h3,
    bernoulli'_four, h5, bernoulli'_six, h7,
    hchoose2, hchoose3, hchoose4, hchoose5, hchoose6]

@[category test, AMS 11]
theorem a_4 : a 4 = 1680 := by
  dsimp [a]
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_eight]
  norm_num

@[category API, AMS 11]
lemma bernoulli'_ten : bernoulli' 10 = 5 / 66 := by
  have hchoose2 : Nat.choose 10 2 = 45 := by decide
  have hchoose3 : Nat.choose 10 3 = 120 := by decide
  have hchoose4 : Nat.choose 10 4 = 210 := by decide
  have hchoose5 : Nat.choose 10 5 = 252 := by decide
  have hchoose6 : Nat.choose 10 6 = 210 := by decide
  have hchoose7 : Nat.choose 10 7 = 120 := by decide
  have hchoose8 : Nat.choose 10 8 = 45 := by decide
  have h3 : bernoulli' 3 = 0 := bernoulli'_three
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by decide)
  have h7 : bernoulli' 7 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by decide)
  have h9 : bernoulli' 9 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by decide)
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_two, h3,
    bernoulli'_four, h5, bernoulli'_six, h7, bernoulli'_eight, h9,
    hchoose2, hchoose3, hchoose4, hchoose5, hchoose6, hchoose7, hchoose8]

@[category test, AMS 11]
theorem a_5 : a 5 = 1188 := by
  dsimp [a]
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_ten]
  norm_num

/-- $A005382(n)$ is the $n$-th prime $p$ such that $2p-1$ is also prime (1-based). -/
noncomputable def a005382 (n : ℕ) : ℕ :=
  Nat.nth (fun p ↦ p.Prime ∧ (2 * p - 1).Prime) (n - 1)

/--
Conjecture I: if $n > 2$, then $\frac{a(\text{A005382}(n))}{12}$ is prime,
where A005382 is the sequence of primes $p$ such that $2p-1$ is also prime.
- Lorenzo Sauras Altuzarra, Oct 13 2020
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : 2 < n) : (a (a005382 n) / 12).Prime := by
  sorry

/--
Conjecture II: if $\frac{a(n)}{12}$ is prime, then $\frac{a(n-1)}{12} - (n-1)$,
$\frac{a(n)}{12} - n$ and $\frac{a(n+2)}{12} - (n+2)$ are multiples of 6.
- Lorenzo Sauras Altuzarra, Oct 13 2020
-/
@[category research open, AMS 11]
theorem conjecture2 (n : ℕ) (hn : 2 ≤ n)
    (h_div : 12 ∣ a n) (h_prime : Nat.Prime (a n / 12))
    (h_div_prev : 12 ∣ a (n - 1)) (h_div_succ : 12 ∣ a (n + 2)) :
    6 ∣ ((a (n - 1) / 12 : ℤ) - (n - 1 : ℤ)) ∧
    6 ∣ ((a n / 12 : ℤ) - (n : ℤ)) ∧
    6 ∣ ((a (n + 2) / 12 : ℤ) - (n + 2 : ℤ)) := by
  sorry

end OeisA46969

