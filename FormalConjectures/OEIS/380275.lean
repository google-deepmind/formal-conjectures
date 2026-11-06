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
# Fourth power sum of $q$-factorial polynomial coefficients

Sum of the fourth powers of the coefficients of $q$ in the $q$-factorials $[n]_q! =
\prod_{j=1}^n \sum_{i=0}^{j-1} q^i$.

*References:*
- [A380275](https://oeis.org/A380275)
-/
open Polynomial Finset Real Asymptotics Filter

namespace OeisA380275

/--
Sum of the fourth powers of the coefficients of $q$ in the $q$-factorials.
The $q$-factorial polynomial $P_n(q)$ is given by
$$P_n(q) = \prod_{j=1}^n \frac{1-q^j}{1-q} = \prod_{j=1}^n \sum_{i=0}^{j-1} q^i$$
The sequence is defined by
$$a(n) : \sum_{k \ge 0} \left([q^k] P_n(q)\right)^4$$
-/
noncomputable def P_q_factorial_poly (n : ℕ) : Polynomial ℕ :=
 (Icc 1 n).prod fun j =>
  -- $\sum_{i=0}^{j-1} X^i$
  ∑ i ∈ range j, C (1 : ℕ) * (X : Polynomial ℕ) ^ i

noncomputable def a (n : ℕ) : ℕ :=
  let P := P_q_factorial_poly n
  -- The maximum degree of $P_n$ is $n(n-1)/2$.
  let max_degree : ℕ := n * (n - 1) / 2

  ∑ k ∈ range (max_degree + 1), (P.coeff k) ^ 4

@[category API, AMS 11]
lemma P_0 : P_q_factorial_poly 0 = 1 := by
  unfold P_q_factorial_poly; rfl

@[category API, AMS 11]
lemma P_1 : P_q_factorial_poly 1 = 1 := by
  unfold P_q_factorial_poly
  have : Icc 1 1 = {1} := rfl
  rw [this, prod_singleton]
  have : range 1 = {0} := rfl
  rw [this, sum_singleton]
  simp

@[category API, AMS 11]
lemma P_2 : P_q_factorial_poly 2 = 1 + X := by
  unfold P_q_factorial_poly
  have : Icc 1 2 = {1, 2} := rfl
  rw [this, prod_insert (by decide), prod_singleton]
  have : range 1 = {0} := rfl
  rw [this, sum_singleton]
  have : range 2 = {0, 1} := rfl
  rw [this, sum_insert (by decide), sum_singleton]
  simp

@[category API, AMS 11]
lemma P_3 : P_q_factorial_poly 3 = 1 + 2 * X + 2 * X ^ 2 + X ^ 3 := by
  unfold P_q_factorial_poly
  have : Icc 1 3 = {1, 2, 3} := rfl
  rw [this, prod_insert (by decide), prod_insert (by decide), prod_singleton]
  have : range 1 = {0} := rfl
  rw [this, sum_singleton]
  have : range 2 = {0, 1} := rfl
  rw [this, sum_insert (by decide), sum_singleton]
  have : range 3 = {0, 1, 2} := rfl
  rw [this, sum_insert (by decide), sum_insert (by decide), sum_singleton]
  simp
  ring

@[category API, AMS 11]
lemma P_4 :
    P_q_factorial_poly 4 = 1 + 3 * X + 5 * X ^ 2 + 6 * X ^ 3 + 5 * X ^ 4 + 3 * X ^ 5 + X ^ 6 := by
  unfold P_q_factorial_poly
  have : Icc 1 4 = {1, 2, 3, 4} := rfl
  rw [this, prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
      prod_singleton]
  have : range 1 = {0} := rfl
  rw [this, sum_singleton]
  have : range 2 = {0, 1} := rfl
  rw [this, sum_insert (by decide), sum_singleton]
  have : range 3 = {0, 1, 2} := rfl
  rw [this, sum_insert (by decide), sum_insert (by decide), sum_singleton]
  have : range 4 = {0, 1, 2, 3} := rfl
  rw [this, sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton]
  simp
  ring

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by
  unfold a
  rw [P_0]
  dsimp
  norm_num

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  unfold a
  rw [P_1]
  dsimp
  norm_num

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by
  unfold a
  rw [P_2]
  dsimp
  simp only [sum_range_succ]
  have h0 : coeff (1 + X : Polynomial ℕ) 0 = 1 := by simp [coeff_one, coeff_X]
  have h1 : coeff (1 + X : Polynomial ℕ) 1 = 1 := by simp [coeff_one, coeff_X]
  rw [h0, h1]
  norm_num

@[category test, AMS 11]
theorem a_3 : a 3 = 34 := by
  unfold a
  rw [P_3]
  dsimp
  simp only [sum_range_succ]
  have h0 : coeff (1 + 2 * X + 2 * X ^ 2 + X ^ 3 : Polynomial ℕ) 0 = 1 :=
    by simp [coeff_one, coeff_X]
  have h1 : coeff (1 + 2 * X + 2 * X ^ 2 + X ^ 3 : Polynomial ℕ) 1 = 2 :=
    by simp [coeff_one, coeff_X]
  have h2 : coeff (1 + 2 * X + 2 * X ^ 2 + X ^ 3 : Polynomial ℕ) 2 = 2 :=
    by simp [coeff_one, coeff_X]
  have h3 : coeff (1 + 2 * X + 2 * X ^ 2 + X ^ 3 : Polynomial ℕ) 3 = 1 :=
    by simp [coeff_one, coeff_X]
  rw [h0, h1, h2, h3]
  norm_num

@[category test, AMS 11]
theorem a_4 : a 4 = 2710 := by
  unfold a
  rw [P_4]
  dsimp
  simp only [sum_range_succ]
  have h0 :
      coeff
        (1 + 3 * X + 5 * X ^ 2 + 6 * X ^ 3 + 5 * X ^ 4 + 3 * X ^ 5 + X ^ 6 : Polynomial ℕ) 0 = 1 :=
    by simp [coeff_one, coeff_X]
  have h1 :
      coeff
        (1 + 3 * X + 5 * X ^ 2 + 6 * X ^ 3 + 5 * X ^ 4 + 3 * X ^ 5 + X ^ 6 : Polynomial ℕ) 1 = 3 :=
    by simp [coeff_one, coeff_X]
  have h2 :
      coeff
        (1 + 3 * X + 5 * X ^ 2 + 6 * X ^ 3 + 5 * X ^ 4 + 3 * X ^ 5 + X ^ 6 : Polynomial ℕ) 2 = 5 :=
    by simp [coeff_one, coeff_X]
  have h3 :
      coeff
        (1 + 3 * X + 5 * X ^ 2 + 6 * X ^ 3 + 5 * X ^ 4 + 3 * X ^ 5 + X ^ 6 : Polynomial ℕ) 3 = 6 :=
    by simp [coeff_one, coeff_X]
  have h4 :
      coeff
        (1 + 3 * X + 5 * X ^ 2 + 6 * X ^ 3 + 5 * X ^ 4 + 3 * X ^ 5 + X ^ 6 : Polynomial ℕ) 4 = 5 :=
    by simp [coeff_one, coeff_X]
  have h5 :
      coeff
        (1 + 3 * X + 5 * X ^ 2 + 6 * X ^ 3 + 5 * X ^ 4 + 3 * X ^ 5 + X ^ 6 : Polynomial ℕ) 5 = 3 :=
    by simp [coeff_one, coeff_X]
  have h6 :
      coeff
        (1 + 3 * X + 5 * X ^ 2 + 6 * X ^ 3 + 5 * X ^ 4 + 3 * X ^ 5 + X ^ 6 : Polynomial ℕ) 6 = 1 :=
    by simp [coeff_one, coeff_X]
  rw [h0, h1, h2, h3, h4, h5, h6]
  norm_num

/-- Generalized sequence: Sum of $k$-th powers of coefficients of $q$-factorial.
We cast to $\mathbb{R}$ for asymptotic analysis. -/
noncomputable def A_k_n (k n : ℕ) : ℝ :=
  let P := P_q_factorial_poly n
  let max_degree : ℕ := n * (n - 1) / 2
  ∑ j ∈ range (max_degree + 1), ((P.coeff j : ℝ) ^ k)

/--
The conjectured asymptotic formula for the sum of $k$-th powers of coefficients of the
$q$-factorial. Note: this function is only relevant for $k>0$ and large $n$.
-/
noncomputable def q_factorial_asymptotic_term_func (k n : ℕ) : ℝ :=
  let k_r : ℝ := k
  let n_r : ℝ := n
  let k_minus_one_half := (k_r - 1) / 2
  -- Define Constant C_k
  let c_k : ℝ :=
    ((2 : ℝ) ^ k_minus_one_half * (3 : ℝ) ^ (k_r - 1)) / (sqrt k_r * Real.pi ^ k_minus_one_half)

  -- Define the N-dependent term
  c_k * ((n.factorial : ℝ) ^ k_r / (n_r ^ (3 * k_minus_one_half)))

/-- Conjecture: In general, sum of the k-th powers of the coefficients of q in the q-factorials
is asymptotic to
$$ 2^{\frac{k-1}{2}} \cdot 3^{k-1} \cdot n!^k / (\sqrt{k} \cdot \pi^{\frac{k-1}{2}} \cdot
   n^{\frac{3(k-1)}{2}}) $$
We require $k > 0$ for the formula to be well-defined (due to $\sqrt{k}$).
Note: Proved by Xinjun Wang (2026).
-/
@[category research solved, AMS 11]
theorem asymptotic_k_th_powers (k : ℕ) (hk : k > 0) :
  Asymptotics.IsEquivalent Filter.atTop (fun n => A_k_n k n) (q_factorial_asymptotic_term_func k) :=
by sorry

end OeisA380275
