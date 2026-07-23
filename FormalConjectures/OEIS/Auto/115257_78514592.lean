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

open Polynomial

/--
A115257: Partial sums of $\binom{2n}{n}^2$.
$$a(n) = \sum_{k=0}^n \binom{2k}{k}^2$$
-/
def a (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum (fun k => (Nat.centralBinom k) ^ 2)

theorem a_zero : a 0 = 1 := by
  rfl

-- These proofs rely on the fact that the sum of small constant terms evaluates correctly.
theorem a_one : a 1 = 5 := by
  rfl

theorem a_two : a 2 = 41 := by
  rfl

theorem a_three : a 3 = 441 := by
  rfl

/-- The polynomial $\sum_{k=0}^{n} \binom{2k}{k}^2 x^k$ over $\mathbb{Q}$. -/
noncomputable
def poly_A115257_P (n : ℕ) : Polynomial ℚ :=
  (Finset.range (n + 1)).sum (fun k => C ((Nat.centralBinom k : ℚ) ^ 2) * X ^ k)

/-- The polynomial $\sum_{k=0}^{n} \frac{\binom{2k}{k}^2}{k+1} x^k$ over $\mathbb{Q}$. -/
noncomputable
def poly_A115257_Q (n : ℕ) : Polynomial ℚ :=
  (Finset.range (n + 1)).sum (fun k => C (((Nat.centralBinom k : ℚ) ^ 2) / (k + 1 : ℚ)) * X ^ k)

/--
Conjecture: For any positive integer n, the polynomials
$\sum_{k=0}^n \binom{2k}{k}^2 x^k$ and $\sum_{k=0}^n \binom{2k}{k}^2 \frac{x^k}{k+1}$
are irreducible over the field of rational numbers. (Zhi-Wei Sun, Mar 23 2013)
-/
theorem oeis_115257_conjecture_0 :
  ∀ (n : ℕ), 1 ≤ n → Irreducible (poly_A115257_P n) ∧ Irreducible (poly_A115257_Q n) := by
  sorry
