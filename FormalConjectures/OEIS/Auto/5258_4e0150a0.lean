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

open Nat

/--
Apéry numbers:
$$a(n) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k}$$
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k ↦ (n.choose k) ^ 2 * ((n + k).choose k)


theorem a_zero : a 0 = 1 := by
  trivial

theorem a_one : a 1 = 3 := by
  subsingleton

theorem a_two : a 2 = 19 := by
  constructor

theorem a_three : a 3 = 147 := by
  rfl


open Polynomial

/--
The polynomial associated with the $n$-th Apéry number:
$$a_n(x) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k} x^k$$
-/
noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

/--
Conjecture: For each n=1,2,3,... the polynomial a_n(x) = Sum_{k=0..n} C(n,k)^2*C(n+k,k)*x^k is irreducible over the field of rational numbers. - _Zhi-Wei Sun_, Mar 21 2013
-/
theorem apery_poly_irreducible (n : ℕ) (hn : 1 ≤ n) : Irreducible (apery_poly n) := by
  sorry
