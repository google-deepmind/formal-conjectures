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
# $a(n) = [x^{2n}] \left(\frac{1 + x}{1 - x}\right)^n$

The sequence is given by the combinatorial identity:
$a(n) = \sum_{k = 0}^n \binom{n}{k} \binom{2n+k-1}{n-1}$
with $a(0) = 1$.

*References:*
- [A103885](https://oeis.org/A103885)
-/

namespace OeisA103885

open Nat Finset Polynomial
open scoped BigOperators ComplexConjugate

/-- The primary defining sequence `a`.
$a(n) = [x^{2n}] \left(\frac{1 + x}{1 - x}\right)^n$, given by the combinatorial identity:
$a(n) = \sum_{k = 0}^n \binom{n}{k} \binom{2n+k-1}{n-1}$
with $a(0) = 1$. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    let r : ℕ := n - 1
    (range (n + 1)).sum (fun k => (n.choose k) * ((2 * n + k - 1).choose r))

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by decide

@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 16 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 146 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 1408 := by decide

/-- The sequence $b(n) = a(m*n)$ lifted to ℝ -/
noncomputable def aSubsequenceReal (m n : ℕ) : ℝ :=
  (a (m * n) : ℝ)

/-- The indices $k = 1$ to $2m$, used in the product -/
private def productIndices (m : ℕ) : Finset ℕ :=
  Finset.Ioc 0 (2 * m)

/-- The factor $\prod_{k=1}^{2m} (2mn + k)$ -/
noncomputable def prodFactorPlus (m n : ℕ) : ℝ :=
  (productIndices m).prod fun k =>
    ((2 * m * n : ℝ) + (k : ℝ))

/-- The factor $\prod_{k=1}^{2m} (2mn - k)$ -/
noncomputable def prodFactorMinus (m n : ℕ) : ℝ :=
  (productIndices m).prod fun k =>
    ((2 * m * n : ℝ) - (k : ℝ))

/--
The recurrence given below can be rewritten in the form
$$(2n+1)(2n+2)P(2,n)a(n+1) - (2n-1)(2n-2)P(2,-n)a(n-1) = Q(2,n^2)a(n),$$
where the polynomial $Q(2,n) = 4(55n^2 - 34n + 3)$ and the polynomial $P(2,n) = 5n^2 - 5n + 1$
satisfies the symmetry condition $P(2,n) = P(2,1-n)$ and has real zeros.
More generally, for fixed $m = 1,2,3, \ldots$, we conjecture that the sequence $b(n) := a(mn)$
satisfies a recurrence of the form
$$( \prod_{k = 1}^{2m} (2mn + k) )P(2m,n)b(n+1) + (-1)^m( \prod_{k = 1}^{2*m} (2mn - k) )
  P(2m,-n)b(n-1) = Q(2m,n^2)b(n),$$
where the polynomials $P(2m,n)$ and $Q(2m,n)$ have degree $2m$. Conjecturally, the polynomial
$P(2m,n) = P(2m,1-n)$ and has real zeros in the interval [0, 1].
The $4m$ zeros of the polynomial $Q(2m,n^2)$ seem to belong to the interval $[-1, 1]$ and
$4m - 2$ of these zeros appear to be approximated by the rational numbers
$\pm k/(3m)$, where $1 \le k \le 3m - 2$, $k$ not a multiple of $3$.
-/
@[category research open, AMS 11]
theorem conjecture (m : ℕ) (hm : 1 ≤ m) :
    ∃ (P Q : Polynomial ℝ),
      -- P and Q have degree 2m
      P.degree = (2 * m : ℕ) ∧ Q.degree = (2 * m : ℕ) ∧
      -- The recurrence relation holds for all n >= 1
      (∀ (n : ℕ) (hn : 1 ≤ n),
        (prodFactorPlus m n * P.eval (n : ℝ)) * (aSubsequenceReal m (n + 1)) +

        ((-1 : ℝ) ^ m * prodFactorMinus m n * P.eval (-(n : ℝ))) * (aSubsequenceReal m (n - 1)) =

        (Q.eval ((n : ℝ)^2)) * (aSubsequenceReal m n)) ∧

      -- P symmetry: P(x) = P(1-x)
      (∀ x : ℝ, P.eval x = P.eval (1 - x)) ∧

      -- P has real zeros in [0, 1]: all complex zeros are real and in [0, 1]
      (∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).eval z = 0 → z.im = 0 ∧ z.re ∈ (Set.Icc 0 1)) ∧

      -- Q zero properties: The zeros of Q(x^2) are real and in [-1, 1].
      (∀ z : ℂ, (Q.map (algebraMap ℝ ℂ)).eval (z^2) = 0 → z.im = 0 ∧ z.re ∈ (Set.Icc (-1) 1)) := by
  sorry

end OeisA103885
