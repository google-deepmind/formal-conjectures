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
# Catalan numbers

Catalan numbers: $C(n) = \binom{2n}{n}/(n+1)$.

*References:*
- [A000108](https://oeis.org/A000108)
-/

namespace OeisA108

open Nat Real Finset Polynomial

/-- The primary defining sequence `a`.
Catalan numbers: $C(n) = \binom{2n}{n}/(n+1)$. -/
def a (n : ℕ) : ℕ := (Nat.choose (2 * n) n) / (n + 1)

-- Reciprocal of the n-th Catalan number as a rational number.
def a_rat (n : ℕ) : ℚ := (a n : ℚ)⁻¹

/-- The sum $\sum_{i=j}^k \frac{1}{a(i)}$ of reciprocals of Catalan numbers. -/
def catalan_reciprocal_sum (j k : ℕ) : ℚ :=
  (Finset.Icc j k).sum a_rat

/-- The index condition on $(j, k)$ from the conjecture: $0 < \min\{2,k\} \le j \le k$.
Since j and k are natural numbers, $0 < \min\{2,k\}$ is equivalent to $1 \le k$. -/
def oeis_108_index_cond (j k : ℕ) : Prop :=
  1 ≤ k ∧ min 2 k ≤ j ∧ j ≤ k

open Int (fract)

/-- The fractional part of a rational number, viewed as a real number. Must be noncomputable
due to dependence on the real floor function. -/
noncomputable def frac_part (q : ℚ) : ℝ := fract (q : ℝ)

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
lemma test_a_0 : a 0 = 1 := by decide

@[category test, AMS 11]
lemma test_a_1 : a 1 = 1 := by decide

@[category test, AMS 11]
lemma test_a_2 : a 2 = 2 := by decide

@[category test, AMS 11]
lemma test_a_3 : a 3 = 5 := by decide

@[category test, AMS 11]
lemma test_a_4 : a 4 = 14 := by decide

/--
A000108 Conjecture: All the rational numbers $\sum_{i=j..k} 1/a(i)$ with $0 < \min\{2,k\} \le j \le k$ have pairwise distinct fractional parts. - _Zhi-Wei Sun_, Sep 24 2015
-/
@[category research open, AMS 11]
theorem conjecture1 :
  ∀ ⦃j₁ k₁ j₂ k₂ : ℕ⦄,
     oeis_108_index_cond j₁ k₁ →
     oeis_108_index_cond j₂ k₂ →
     (j₁, k₁) ≠ (j₂, k₂) →
     frac_part (catalan_reciprocal_sum j₁ k₁) ≠ frac_part (catalan_reciprocal_sum j₂ k₂)
  := by sorry

/--
The polynomial $\sum_{k=0}^n a(k) x^k$, where $a(k)$ are the Catalan numbers.
The coefficients $a(k) \in \mathbb{N}$ are coerced to $\mathbb{Q}$.
-/
noncomputable def catalan_polynomial (n : ℕ) : ℚ[X] :=
  (Finset.range (n + 1)).sum (fun k => C (a k : ℚ) * X^k)

/--
OEIS A000108 Conjecture: For any positive integer n, the polynomial
Sum_{k=0..n} a(k)*x^k is irreducible over the field of rational numbers.
-/
@[category research open, AMS 11 12]
theorem conjecture2 (n : ℕ) (h : n > 0) :
    Irreducible (catalan_polynomial n) := by
  sorry

end OeisA108
