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
# Coefficients of $\prod_{k>0} (1 - x^k/k!)$

The sequence $a(n)$ has exponential generating function
$$E(x) = \prod_{k=1}^\infty \left(1 - \frac{x^k}{k!}\right),$$
so that $a(n) = n! [x^n] \prod_{k=1}^n \left(1 - \frac{x^k}{k!}\right)$.

*References:*
- [A185895](https://oeis.org/A185895)
-/

open Polynomial



namespace OeisA185895

/-- The finite polynomial approximation $\prod_{k=1}^n (1 - X^k / k!)$. -/
noncomputable def P (n : ℕ) : Polynomial ℚ :=
  ∏ k ∈ Finset.Icc 1 n, (1 - C (1 / (k.factorial : ℚ)) * X ^ k)

/-- The sequence $a(n) = n! [x^n] \prod_{k=1}^n (1 - x^k / k!)$. -/
noncomputable def a (n : ℕ) : ℤ :=
  if n = 0 then 1
  else (coeff (P n) n * (n.factorial : ℚ)).floor

/-- A natural number $n$ is triangular if $n = k(k+1)/2$ for some $k \in \mathbb{N}$. -/
def IsTriangular (n : ℕ) : Prop := ∃ k : ℕ, n = k * (k + 1) / 2

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by rfl

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = -1 := by
  dsimp [a, P]
  simp [coeff_one]
  rfl

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = -1 := by
  dsimp [a, P]
  have hI : (Finset.Icc 1 2 : Finset ℕ) = {1, 2} := by decide
  rw [hI, Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [mul_sub, sub_mul, one_mul, mul_one, coeff_sub, coeff_add, coeff_one,
    coeff_X_pow, coeff_X, coeff_C_mul_X_pow]
  norm_num

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by
  dsimp [a, P]
  have hI : (Finset.Icc 1 3 : Finset ℕ) = {1, 2, 3} := by decide
  have h_prod : (∏ k ∈ Finset.Icc 1 3, (1 - C (1 / (k.factorial : ℚ)) * X ^ k)) =
      1 - X - C (1/2 : ℚ) * X ^ 2 + C (1/3 : ℚ) * X ^ 3 + C (1/6 : ℚ) * X ^ 4 - C (1/12 : ℚ) * X ^ 5 := by
    rw [hI, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
    ring
  rw [h_prod]
  simp [sub_mul, mul_sub, coeff_sub, coeff_add, coeff_one, coeff_X, coeff_X_pow]
  rfl

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 3 := by
  dsimp [a, P]
  have hI : (Finset.Icc 1 4 : Finset ℕ) = {1, 2, 3, 4} := by decide
  have h_prod : (∏ k ∈ Finset.Icc 1 4, (1 - C (1 / (k.factorial : ℚ)) * X ^ k)) =
      1 - X - C (1/2 : ℚ) * X ^ 2 + C (1/3 : ℚ) * X ^ 3 + C (1/8 : ℚ) * X ^ 4 -
      C (1/24 : ℚ) * X ^ 5 + C (1/48 : ℚ) * X ^ 6 - C (1/72 : ℚ) * X ^ 7 -
      C (1/144 : ℚ) * X ^ 8 + C (1/288 : ℚ) * X ^ 9 := by
    rw [hI, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_singleton]
    ring
  rw [h_prod]
  simp [sub_mul, mul_sub, coeff_sub, coeff_add, coeff_one, coeff_X, coeff_X_pow]
  rfl

/--
$a(n)$ differs in sign from $a(n-1)$ if and only if $n$ is a triangular number
(checked up to $n = 1225 = (50 \cdot 51)/2$).
- _Peter Bala_, Mar 17 2022
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 0 < n) :
    a n * a (n - 1) < 0 ↔ IsTriangular n := by
  sorry

end OeisA185895
