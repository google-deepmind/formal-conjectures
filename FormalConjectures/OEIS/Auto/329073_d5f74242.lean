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
T_k(b, c) is the coefficient of $x^k$ in the expansion of $(x^2 + b x + c)^k$.
$$T_k(b, c) = \sum_{i=0}^{\lfloor k/2 \rfloor} \binom{k}{i} \binom{k-i}{i} b^{k-2i} c^i$$
where $k \in \mathbb{N}$ and $b, c \in \mathbb{Z}$.
-/
def T_coeff (k : ℕ) (b c : ℤ) : ℤ :=
  (range (k / 2 + 1)).sum fun i : ℕ =>
    let choose_term : ℤ := (k.choose i).cast * ((k - i).choose i).cast
    let b_pow : ℤ := b ^ (k - 2 * i)
    let c_pow : ℤ := c ^ i
    choose_term * b_pow * c_pow

/--
A329073: $a(n) = (1/n)*\sum_{k=0}^{n-1} (40k+13)*(-1)^k*50^{n-1-k}*T_k(4,1)*T_k(1,-1)^2$,
where $T_k(b,c)$ denotes the coefficient of $x^k$ in the expansion of $(x^2+b*x+c)^k$.
The sequence is conjectured to consist of integers, so we use integer division.
-/
def A329073 (n : ℕ) : ℤ :=
  match n with
  | 0 => 0
  | N@(_ + 1) => -- N is n+1, so $N \ge 1$.
    let N_int : ℤ := N.cast
    let sum_val : ℤ := (range N).sum fun k : ℕ =>
      let k_int : ℤ := k.cast
      let coeff_a : ℤ := T_coeff k 4 1
      let coeff_b : ℤ := T_coeff k 1 (-1)

      let term_1 := (40 * k_int + 13)
      let term_2 := (-1 : ℤ) ^ k
      let term_3_exp : ℕ := N - 1 - k
      let term_3 := (50 : ℤ) ^ term_3_exp

      term_1 * term_2 * term_3 * coeff_a * (coeff_b ^ 2)

    sum_val / N_int

/--
b(n) is the sequence related to A329073 defined as:
b(n) := (1/n)*Sum_{k=0..n-1} (40k+27)*(-6)^(n-1-k)*T_k(4,1)*T_k(1,-1)^2
It is conjectured to be an integer.
-/
def A329073_b (n : ℕ) : ℤ :=
  match n with
  | 0 => 0
  | N@(_ + 1) => -- N is n+1, so $N \ge 1$.
    let N_int : ℤ := N.cast
    let sum_val : ℤ := (range N).sum fun k : ℕ =>
      let k_int : ℤ := k.cast
      let coeff_a : ℤ := T_coeff k 4 1
      let coeff_b : ℤ := T_coeff k 1 (-1)

      let term_1 := (40 * k_int + 27)
      let term_3_exp : ℕ := N - 1 - k
      let term_3 := ((-6) : ℤ) ^ term_3_exp

      term_1 * term_3 * coeff_a * (coeff_b ^ 2)

    sum_val / N_int

theorem a_one : A329073 1 = 13 := by
  rfl

-- Remaining placeholder theorems for A329073 omitted for brevity, as requested.

/--
A329073 Conjecture 2: (i) For any n > 0, the number b(n):=(1/n)*Sum_{k=0..n-1} (40k+27)*(-6)^(n-1-k)*T_k(4,1)*T_k(1,-1)^2 is an integer. Moreover, b(n) is odd if and only if n is a power of two.
-/
theorem oeis_329073_conjecture_2_i :
  ∀ (n : ℕ), 0 < n →
  (A329073_b n = A329073_b n) ∧ -- The definition of A329073_b uses integer division, implying the first part of the conjecture is an integrality statement on the quotient, which is implicitly handled by the `ℤ` return type. We should state the divisibility explicitly to make it a statement about $\mathbb{Z}$-valued functions, but since the sequence is defined using integer division and we are formalizing the conjecture about the existence of an integer value, we should focus on the property of the quotient being an integer. In combinatorics contexts, stating a rational number is an integer often means the numerator is divisible by the denominator.
  -- Let's rephrase the first part of the conjecture "b(n) is an integer" as the fact that the division is exact.
  -- b(n) is always an integer if its definition is $(1/n) * \text{Sum} \dots \in \mathbb{Z}$.
  -- The expression `sum_val / N_int` is $\lfloor \frac{\text{sum}}{n} \rfloor$.
  -- The conjecture is that $\text{sum}$ is divisible by $n$.
  ((n.cast : ℤ) ∣ ( (range n).sum fun k : ℕ =>
    let k_int : ℤ := k.cast
    let coeff_a : ℤ := T_coeff k 4 1
    let coeff_b : ℤ := T_coeff k 1 (-1)
    let term_1 := (40 * k_int + 27)
    let term_3_exp : ℕ := n - 1 - k
    let term_3 := ((-6) : ℤ) ^ term_3_exp
    term_1 * term_3 * coeff_a * (coeff_b ^ 2) )) ∧
  -- Moreover b(n) is odd if and only if n is a power of two.
  (A329073_b n % 2 = 1 ↔ Nat.isPowerOfTwo n)
  := by sorry
