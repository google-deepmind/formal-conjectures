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

open Nat Finset Polynomial
open scoped BigOperators ComplexConjugate

/--
A103885: $a(n) = [x^{2n}] \left(\frac{1 + x}{1 - x}\right)^n$.
The sequence is given by the combinatorial identity:
$$a(n) = \sum_{k = 0}^n \binom{n}{k} \binom{2n+k-1}{n-1}$$
with $a(0) = 1$.
-/
def A103885 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    let r : ℕ := n - 1
    (range (n + 1)).sum (fun k => (n.choose k) * ((2 * n + k - 1).choose r))


theorem a_zero : A103885 0 = 1 := by
  simp [A103885]

theorem a_one : A103885 1 = 2 := by
  sorry

theorem a_two : A103885 2 = 16 := by
  sorry

theorem a_three : A103885 3 = 146 := by
  sorry

-- The sequence b(n) = a(m*n) lifted to ℝ
noncomputable def A103885_subsequence_real (m n : ℕ) : ℝ :=
  (A103885 (m * n) : ℝ)

open BigOperators

-- The indices k = 1 to 2m, used in the product
private def product_indices (m : ℕ) : Finset ℕ :=
  Finset.Ioc 0 (2 * m)

-- The factor Product_{k=1}^{2m} (2mn + k)
noncomputable def prod_factor_plus (m n : ℕ) : ℝ :=
  (product_indices m).prod fun k =>
    ((2 * m * n : ℝ) + (k : ℝ))

-- The factor Product_{k=1}^{2m} (2mn - k)
noncomputable def prod_factor_minus (m n : ℕ) : ℝ :=
  (product_indices m).prod fun k =>
    ((2 * m * n : ℝ) - (k : ℝ))

/--
The recurrence given below can be rewritten in the form
(2*n+1)*(2*n+2)*P(2,n)*a(n+1) - (2*n-1)*(2*n-2)*P(2,-n)*a(n-1) = Q(2,n^2)*a(n), where the polynomial Q(2,n) = 4*(55*n^2 - 34*n + 3) and the polynomial P(2,n) = 5*n^2 - 5*n + 1 satisfies the symmetry condition P(2,n) = P(2,1-n) and has real zeros.
More generally, for fixed m = 1,2,3,..., we conjecture that the sequence b(n) := a(m*n) satisfies a recurrence of the form ( Product_{k = 1..2*m} (2*m*n + k) ) * P(2*m,n)*b(n+1) + (-1)^m*( Product_{k = 1..2*m} (2*m*n - k) ) * P(2*m,-n)*b(n-1) = Q(2*m,n^2)*b(n), where the polynomials P(2*m,n) and Q(2*m,n) have degree 2*m. Conjecturally, the polynomial P(2*m,n) = P(2*m,1-n) and has real zeros in the interval [0, 1]. The 4*m zeros of the polynomial Q(2*m,n^2) seem to belong to the interval [-1, 1] and 4*m - 2 of these zeros appear to be approximated by the rational numbers +- k/(3*m), where 1 <= k <= 3*m - 2, k not a multiple of 3.
-/
theorem oeis_a103885_conjecture_0 (m : ℕ) (hm : 1 ≤ m) :
    ∃ (P Q : Polynomial ℝ),
      -- P and Q have degree 2m
      P.degree = (2 * m : ℕ) ∧ Q.degree = (2 * m : ℕ) ∧
      -- The recurrence relation holds for all n >= 1
      (∀ (n : ℕ) (hn : 1 ≤ n),
        (prod_factor_plus m n * P.eval (n : ℝ)) * (A103885_subsequence_real m (n + 1)) +

        ((-1 : ℝ) ^ m * prod_factor_minus m n * P.eval (-(n : ℝ))) * (A103885_subsequence_real m (n - 1)) =

        (Q.eval ((n : ℝ)^2)) * (A103885_subsequence_real m n)) ∧

      -- P symmetry: P(x) = P(1-x)
      (∀ x : ℝ, P.eval x = P.eval (1 - x)) ∧

      -- P has real zeros in [0, 1]: all complex zeros are real and in [0, 1]
      (∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).eval z = 0 → z.im = 0 ∧ z.re ∈ (Set.Icc 0 1)) ∧

      -- Q zero properties: The zeros of Q(x^2) are real and in [-1, 1].
      (∀ z : ℂ, (Q.map (algebraMap ℝ ℂ)).eval (z^2) = 0 → z.im = 0 ∧ z.re ∈ (Set.Icc (-1) 1)) :=
  by sorry
