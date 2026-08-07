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

open BigOperators Matrix Nat

/--
A005259: The auxiliary sequence used for the Hankel matrix, defined as
$$\sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k}^2$$
-/
def A005259' (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (n.choose k)^2 * ((Nat.choose (n + k) k))^2

/--
A228143: Determinant of the $(n+1) \times (n+1)$ Hankel-type matrix with $(i,j)$-entry equal to A005259$(i+j)$ for all $i,j = 0,\dots,n$.
The entry function A005259 is taken to be $\sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k}^2$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let dim : Type := Fin (n + 1)
  -- Matrix entries are lifted to ℤ for determinant calculation
  let M : Matrix dim dim ℤ :=
    Matrix.of fun i j => (A005259' (i.val + j.val) : ℤ)
  -- The sequence is known to be non-negative integers (nonn).
  M.det.natAbs


theorem a_zero : a 0 = 1 := by rfl
theorem a_one : a 1 = 48 := by sorry
theorem a_two : a 2 = 161856 := by sorry
theorem a_three : a 3 = 39002646528 := by sorry

open PowerSeries

/-- The power series $A(x/3) = \sum_{n=0}^\infty \frac{a(n)}{3^n} x^n$ over ℚ. -/
noncomputable def OGF_A_scaled : PowerSeries ℚ :=
  PowerSeries.mk fun n => (a n : ℚ) / (3 ^ n : ℚ)

/--
A228143 Conjecture: if $A(x) = 1 + 48*x + 161856*x^2 + \dots$ denotes the o.g.f. then
$A(x/3)^{1/8}$ has integer coefficients (checked up to $x^{30}$).

This is formalized as: there exists a power series $C(x)$ over $\mathbb{Z}$ such that $C(x)^8 = A(x/3)$.
The map `PowerSeries.map (Int.castRingHom ℚ)` lifts the power series from $\mathbb{Z}[[X]]$ to $\mathbb{Q}[[X]]$.
-/
theorem oeis_228143_conjecture_1 :
    ∃ C : PowerSeries ℤ,
      (PowerSeries.map (Int.castRingHom ℚ)) (C ^ 8) = OGF_A_scaled :=
  by sorry
