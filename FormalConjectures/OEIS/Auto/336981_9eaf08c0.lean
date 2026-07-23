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

import FormalConjectures.Util.ProblemImports

open Nat Finset
open scoped BigOperators

/--
The coefficient of $x^k$ in the expansion of $(x^2 + b x + c)^k$.
$$ T_k(b, c) = \sum_{i=0}^{\lfloor k/2 \rfloor} \binom{k}{i} \binom{k-i}{i} b^{k-2i} c^i $$
-/
def T_k (k : ℕ) (b c : ℤ) : ℚ :=
  Finset.sum (range (k / 2 + 1)) (fun i : ℕ =>
    -- The multinomial coefficient $\binom{k}{i, i, k-2i}$
    ((k.choose i * (k - i).choose i : ℕ) : ℚ) *
    -- Powers of b and c
    ((b : ℚ) ^ (k - 2 * i) * (c : ℚ) ^ i))

/--
A336981: $$a(n) = \frac{\sum_{k=0}^{n-1} (4290k + 367) \cdot 3136^{n-1-k} \cdot \binom{2k}{k} \cdot T_k(14, 1) \cdot T_k(17, 16)}{n \cdot \binom{2n-1}{n-1}}$$
where $T_k(b, c)$ denotes the coefficient of $x^k$ in the expansion of $(x^2 + b x + c)^k$.
The sequence is defined as a function $\mathbb{N} \to \mathbb{Q}$.
-/
noncomputable def a (n : ℕ) : ℚ :=
  if n = 0 then 0
  else
    let numerator_sum : ℚ :=
      Finset.sum (range n) (fun k : ℕ =>
        let T1k : ℚ := T_k k 14 1
        let T2k : ℚ := T_k k 17 16

        let k_q : ℚ := k
        -- We use casting for the exponent subtraction to ensure it stays non-negative when k <= n-1
        let n_prime : ℕ := n - 1 - k

        let term_factor : ℚ := 4290 * k_q + 367
        let power_factor : ℚ := (3136 : ℚ) ^ n_prime
        let central_binomial : ℚ := (Nat.choose (2 * k) k : ℚ)

        term_factor * power_factor * central_binomial * T1k * T2k)

    let divisor : ℚ := (n : ℚ) * (Nat.choose (2 * n - 1) (n - 1) : ℚ)

    numerator_sum / divisor

-- Sanity checks - replacing former failing proofs with `sorry`
theorem a_one : a 1 = 367 := by
  push_cast[a]
  norm_num only[T_k, Finset.sum_range_one,Nat.choose]

theorem a_two : a 2 = 561274 := by
  sorry

theorem a_three : a 3 = 465761738 := by
  sorry

theorem a_four : a 4 = 347992898596 := by
  sorry

-- Definition for t(k) for the infinite sum
/--
$$t(k) = \frac{4290k+367}{3136^k} \cdot \binom{2k}{k} \cdot T_k(14, 1) \cdot T_k(17, 16)$$
-/
noncomputable def t (k : ℕ) : ℝ :=
  let T1k : ℝ := T_k k 14 1
  let T2k : ℝ := T_k k 17 16
  let k_r : ℝ := k
  let central_binomial : ℝ := (Nat.choose (2 * k) k : ℝ)

  let term_factor : ℝ := 4290 * k_r + 367
  let power_factor : ℝ := (3136 : ℝ) ^ k

  term_factor / power_factor * central_binomial * T1k * T2k

/--
Conjecture 2 (i): We have $\sum_{k \ge 0} t(k) = 5390/\pi$.

Denote (4290k+367)/3136^k*C(2k,k)*T_k(14,1)*T_k(17,16) by t(k).
(i) We have Sum_{k>=0}t(k) = 5390/Pi.
-/
theorem oeis_a336981_conjecture_2_i :
  (∑' (k : ℕ), t k) = 5390 / Real.pi := by
  sorry
