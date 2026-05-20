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

open scoped BigOperators
open Rat

/--
The $k$-th term of the sum in A281820, defined to be 0 when $k=0$.
$$ T_k = \frac{30k-11}{4(2k-1)k^3 \binom{2k}{k}^2} $$
-/
def A281820_term (k : ℕ) : ℚ :=
  if k = 0 then 0
  else
    let k_q : ℚ := k

    -- Numerator: 30k - 11
    let numerator : ℚ := (30 : ℚ) * k_q - 11

    -- Denominator: 4 * (2k-1) * k^3 * binomial(2k,k)^2
    let denominator : ℚ :=
      (4 : ℚ) * ((2 : ℚ) * k_q - 1) * (k_q ^ 3) * ((Nat.choose (2 * k) k) : ℚ) ^ 2

    numerator / denominator

/--
A281820: Numerator of $\sum_{k=1}^n \frac{30k-11}{4(2k-1)k^3 \binom{2k}{k}^2}$.
The sum over $k=1$ to $n$ is computed using $\sum_{k=0}^n$ since $\text{A281820\_term}(0) = 0$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let sum_q : ℚ := Finset.sum (Finset.range (n + 1)) A281820_term
  sum_q.num.natAbs

/--
A281821: Denominator of $\sum_{k=1}^n \frac{30k-11}{4(2k-1)k^3 \binom{2k}{k}^2}$.
-/
noncomputable def A281821 (n : ℕ) : ℕ :=
  let sum_q : ℚ := Finset.sum (Finset.range (n + 1)) A281820_term
  sum_q.den

-- Placeholders for proof checks, not required to be proven.
theorem a_one : a 1 = 19 := by sorry
theorem a_two : a 2 = 4153 := by sorry
theorem a_three : a 3 = 519283 := by sorry
theorem a_four : a 4 = 1424927267 := by sorry


open Real BigOperators

/-- Apery's constant $\zeta(3) = \sum_{n=1}^\infty 1/n^3$. -/
noncomputable def zeta_three : ℝ :=
  ∑' n : ℕ, if n = 0 then 0 else 1 / (n : ℝ) ^ 3

/--
The term for the first sum in the conjecture:
$$ \frac{1}{n^3 \prod_{j=1}^k (n^2 - j^2)^2} $$
Note: This term is only defined for $n > k$.
-/
noncomputable def conj_term_1 (k n : ℕ) : ℝ :=
  if n ≤ k then 0
  else
    let n_r : ℝ := n
    -- The product $\prod_{j=1}^k$
    let product_sq_terms : ℝ := Finset.prod (Finset.Icc 1 k) (fun j : ℕ => (n_r^2 - ((j : ℝ) ^ 2)) ^ 2)
    1 / (n_r ^ 3 * product_sq_terms)

/--
The term for the second sum in the conjecture:
$$ \frac{1}{n \binom{n}{k}^2 \binom{n+k}{k}^2 (n-k)^2} $$
Note: This term is only defined for $n > k$.
-/
noncomputable def conj_term_2 (k n : ℕ) : ℝ :=
  if n ≤ k then 0
  else
    let n_r : ℝ := n
    let k_r : ℝ := k

    -- $\binom{n}{k}^2$
    let binom_nk_sq : ℝ := ((Nat.choose n k) : ℝ) ^ 2

    -- $\binom{n+k}{k}^2$
    let binom_npk_sq : ℝ := ((Nat.choose (n + k) k) : ℝ) ^ 2

    -- $(n-k)^2$
    let diff_sq : ℝ := (n_r - k_r) ^ 2

    1 / (n_r * binom_nk_sq * binom_npk_sq * diff_sq)

/--
A281820 Conjecture: Sum_{n >= k+1} 1/(n^3*(n^2 - 1)^2*(n^2 - 4)^2*...*(n^2 - k^2)^2) = Sum_{n >= k+1} 1/(n*binomial(n,k)^2*binomial(n+k,k)^2*(n-k)^2) = zeta(3) - A281820(k)/A281821(k). - _Peter Bala_, Jan 17 2022
-/
theorem oeis_281820_conjecture_0 (k : ℕ) (hk : 1 ≤ k) :
    (∑' n : ℕ, conj_term_1 k n) = (∑' n : ℕ, conj_term_2 k n) ∧
    (∑' n : ℕ, conj_term_1 k n) = zeta_three - (a k : ℝ) / (A281821 k : ℝ) :=
  by sorry
