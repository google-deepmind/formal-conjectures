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

open Polynomial Finset Real Asymptotics Filter

-- [START USER PROVIDED CODE]
/--
A380275: Sum of the fourth powers of the coefficients of $q$ in the $q$-factorials.
The $q$-factorial polynomial $P_n(q)$ is given by
$$P_n(q) = \prod_{j=1}^n \frac{1-q^j}{1-q} = \prod_{j=1}^n \sum_{i=0}^{j-1} q^i$$
The sequence is defined by
$$a(n) : \sum_{k \ge 0} \left([q^k] P_n(q)\right)^4$$
-/
noncomputable def P_q_factorial_poly (n : ℕ) : Polynomial ℕ :=
 (Icc 1 n).prod fun j =>
  -- $\sum_{i=0}^{j-1} X^i$
  (Finset.range j).sum fun i => C (1 : ℕ) * (X : Polynomial ℕ) ^ i

noncomputable def a (n : ℕ) : ℕ :=
  let P := P_q_factorial_poly n
  -- The maximum degree of $P_n$ is $n(n-1)/2$.
  let max_degree : ℕ := n * (n - 1) / 2

  Finset.sum (Finset.range (max_degree + 1)) fun k => (P.coeff k) ^ 4


theorem a_zero : a 0 = 1 := by sorry
theorem a_one : a 1 = 1 := by sorry
theorem a_two : a 2 = 2 := by sorry
theorem a_three : a 3 = 34 := by sorry
-- [END USER PROVIDED CODE]

/-- Generalized sequence: Sum of $k$-th powers of coefficients of $q$-factorial.
We cast to $\mathbb{R}$ for asymptotic analysis. -/
noncomputable def A_k_n (k n : ℕ) : ℝ :=
  let P := P_q_factorial_poly n
  let max_degree : ℕ := n * (n - 1) / 2
  (Finset.range (max_degree + 1)).sum fun j : ℕ => ((P.coeff j : ℝ) ^ k)

/-- The conjectured asymptotic formula for the sum of $k$-th powers of coefficients of the $q$-factorial.
Note: this function is only relevant for $k>0$ and large $n$. -/
noncomputable def q_factorial_asymptotic_term_func (k n : ℕ) : ℝ :=
  let k_r : ℝ := k
  let n_r : ℝ := n
  let k_minus_one_half := (k_r - 1) / 2
  -- Define Constant C_k
  let c_k : ℝ := ((2 : ℝ) ^ k_minus_one_half * (3 : ℝ) ^ (k_r - 1)) / (sqrt k_r * Real.pi ^ k_minus_one_half)

  -- Define the N-dependent term
  c_k * ((n.factorial : ℝ) ^ k_r / (n_r ^ (3 * k_minus_one_half)))

/-- oeis_380275_conjecture_general:
Conjecture: In general, sum of the k-th powers of the coefficients of q in the q-factorials
is asymptotic to
$$ 2^{\frac{k-1}{2}} \cdot 3^{k-1} \cdot n!^k / (\sqrt{k} \cdot \pi^{\frac{k-1}{2}} \cdot n^{\frac{3(k-1)}{2}}) $$
We require $k > 0$ for the formula to be well-defined (due to $\sqrt{k}$).
-/
theorem oeis_380275_conjecture_general (k : ℕ) (hk : k > 0) :
  Asymptotics.IsEquivalent Filter.atTop (fun n => A_k_n k n) (q_factorial_asymptotic_term_func k) :=
by sorry
