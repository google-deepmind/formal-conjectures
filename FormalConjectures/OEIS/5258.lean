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
# Apéry numbers

Apéry numbers:
$$a(n) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k}$$

*References:*
- [A005258](https://oeis.org/A005258)
-/

namespace OeisA5258

/-- Apéry numbers: $a(n) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k}$. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), n.choose k ^ 2 * (n + k).choose k

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 3 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 19 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 147 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 1251 := by rfl

open Polynomial in
/-- The polynomial associated with the $n$-th Apéry number:
$a_n(x) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k} x^k$. -/
noncomputable def aperyPoly (n : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * X ^ k

/--
For each $n = 1, 2, 3, \dots$ the polynomial
$a_n(x) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k} x^k$
is irreducible over the field of rational numbers.
- Zhi-Wei Sun, Mar 21 2013
-/
@[category research open, AMS 11 12]
theorem conjecture (n : ℕ) (hn : 1 ≤ n) : Irreducible (aperyPoly n) := by
  sorry

end OeisA5258
