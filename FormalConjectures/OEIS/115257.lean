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
# Partial sums of binomial(2n,n)^2.

Partial sums of $\binom{2n}{n}^2$.
$$a(n) = \sum_{k=0}^n \binom{2k}{k}^2$$

*References:*
- [A115257](https://oeis.org/A115257)
-/

namespace OeisA115257

open Polynomial

/--
The primary defining sequence `a`.
Partial sums of $\binom{2n}{n}^2$.
-/
def a (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum (fun k => (Nat.centralBinom k) ^ 2)

@[category test, AMS 11]
lemma test_a_0 : a 0 = 1 := by rfl

@[category test, AMS 11]
lemma test_a_1 : a 1 = 5 := by rfl

@[category test, AMS 11]
lemma test_a_2 : a 2 = 41 := by rfl

@[category test, AMS 11]
lemma test_a_3 : a 3 = 441 := by rfl

/-- The polynomial $\sum_{k=0}^{n} \binom{2k}{k}^2 x^k$ over $\mathbb{Q}$. -/
noncomputable
def poly_P (n : ℕ) : Polynomial ℚ :=
  (Finset.range (n + 1)).sum (fun k => C ((Nat.centralBinom k : ℚ) ^ 2) * X ^ k)

/-- The polynomial $\sum_{k=0}^{n} \frac{\binom{2k}{k}^2}{k+1} x^k$ over $\mathbb{Q}$. -/
noncomputable
def poly_Q (n : ℕ) : Polynomial ℚ :=
  (Finset.range (n + 1)).sum (fun k => C (((Nat.centralBinom k : ℚ) ^ 2) / (k + 1 : ℚ)) * X ^ k)

/--
Conjecture: For any positive integer n, the polynomials Sum_{k=0}^n binomial(2k,k)^2*x^k and Sum_{k=0}^n binomial(2k,k)^2*x^k/(k+1) are irreducible over the field of rational numbers. - Zhi-Wei Sun, Mar 23 2013
-/
@[category research open, AMS 11]
theorem main_conjecture :
  ∀ (n : ℕ), 1 ≤ n → Irreducible (poly_P n) ∧ Irreducible (poly_Q n) := by
  sorry

end OeisA115257
