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

@[category API, AMS 11]
lemma C_mul_X_pow_mul (a b : ℚ) (n m : ℕ) :
    (C a * X ^ n) * (C b * X ^ m) = C (a * b) * X ^ (n + m) := by
  rw [C_mul, pow_add]
  ring

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
  simp only [mul_sub, sub_mul, one_mul, mul_one, C_mul_X_pow_mul,
    coeff_sub, coeff_one, coeff_C_mul_X_pow]
  decide +native

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by
  dsimp [a, P]
  have hI : (Finset.Icc 1 3 : Finset ℕ) = {1, 2, 3} := by decide
  rw [hI, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [mul_sub, sub_mul, one_mul, mul_one, C_mul_X_pow_mul,
    coeff_sub, coeff_one, coeff_C_mul_X_pow]
  decide +native

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 3 := by
  dsimp [a, P]
  have hI : (Finset.Icc 1 4 : Finset ℕ) = {1, 2, 3, 4} := by decide
  rw [hI, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [mul_sub, sub_mul, one_mul, mul_one, C_mul_X_pow_mul,
    coeff_sub, coeff_one, coeff_C_mul_X_pow]
  decide +native

/-- The $n$-th coefficient of the square of the ordinary generating function $A(x)^2$. -/
noncomputable def c (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), a k * a (n - k)

/--
$a(n)$ differs in sign from $a(n-1)$ if and only if $n$ is a triangular number
(checked up to $n = 1225 = (50 \cdot 51)/2$).
- _Peter Bala_, Mar 17 2022
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : 0 < n) :
    a n * a (n - 1) < 0 ↔ IsTriangular n := by
  sorry

/--
The coefficients $c(n)$ of $A(x)^2 = (\sum_{n \ge 0} a(n) x^n)^2$ differ in sign from $c(n-1)$
if and only if $n$ is a triangular number.
- _Peter Bala_, Mar 17 2022
-/
@[category research open, AMS 11]
theorem conjecture2 (n : ℕ) (hn : 0 < n) :
    c n * c (n - 1) < 0 ↔ IsTriangular n := by
  sorry

/--
The Gauss congruences $a(n \cdot p^k) \equiv a(n \cdot p^{k-1}) \pmod{p^k}$ hold
for all primes $p$ and positive integers $n$ and $k$.
- _Peter Bala_, Mar 17 2022
-/
@[category research open, AMS 11]
theorem conjecture3 (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ k] := by
  sorry

end OeisA185895

