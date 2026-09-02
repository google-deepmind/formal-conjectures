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

open Polynomial Nat Finset

/--
A185895: Exponential generating function is $\prod_{k>0} (1 - x^k/k!).$
The $n$-th term is
$$ a(n) = n! \cdot \left[x^n\right] \left( \prod_{k=1}^n \left(1 - \frac{x^k}{k!}\right) \right) $$
The coefficients $a(n)$ are integers.
-/
noncomputable def A185895 (n : ℕ) : ℤ :=
  if n = 0 then 1 else
  -- n! is defined for n=0, and Px_0 is 1, so a(0) = 1.
  -- We handle n=0 explicitly to avoid issues with 0.factorial.cast in the general case if k=0 were included.

  -- The finite product $\prod_{k=1}^n \left(1 - \frac{x^k}{k!}\right)$ is equivalent to the infinite product for the coefficient of $x^n$.
  let Px : Polynomial ℚ := (Icc 1 n).prod (fun k : ℕ =>
    -- Factor is $1 - x^k/k!$.
    (1 : Polynomial ℚ) - C ((1 : ℚ) / k.factorial.cast) * X ^ k)

  -- $[x^n] Px$ is the coefficient of $x^n$.
  let coeff_n : ℚ := Polynomial.coeff Px n

  -- $a(n) = n! \cdot [x^n] Px$.
  let a_n_q : ℚ := coeff_n * n.factorial.cast

  -- The result is an integer, so Rat.floor converts the rational value to ℤ.
  a_n_q.floor


theorem a_zero : A185895 0 = 1 := by
  constructor

theorem a_one : A185895 1 = -1 := by sorry

theorem a_two : A185895 2 = -1 := by sorry

theorem a_three : A185895 3 = 2 := by sorry

/-- A natural number $n$ is a triangular number if it is of the form $k(k+1)/2$ for some $k \in \mathbb{N}$. -/
def is_triangular (n : ℕ) : Prop := ∃ k : ℕ, n = k * (k + 1) / 2

/--
Conjectures: 1) a(n) differs in sign from a(n-1) iff n is a triangular number (checked up to n = 1225 = (50*51)/2)
The condition "differs in sign" for $a(n)$ and $a(n-1)$ is formalized as their product being strictly negative.
We only consider $n \ge 1$.
-/
theorem oeis_185895_conjecture_1 :
  ∀ (n : ℕ), 0 < n →
    ((A185895 n) * (A185895 (n - 1)) < 0 ↔ is_triangular n) := by
  sorry
