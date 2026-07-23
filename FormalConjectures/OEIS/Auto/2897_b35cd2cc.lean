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

open Nat MvPolynomial

/--
The sequence $a(n)$ is defined by $a(n) = \binom{2n}{n}^3$.
We use `Nat.choose (2 * n) n` for the central binomial coefficient.
-/
def a (n : ℕ) : ℕ := (Nat.choose (2 * n) n) ^ 3

-- The boilerplate theorems provided in the prompt, adapted to the definition.
theorem a_zero : a 0 = 1 := by decide
theorem a_one : a 1 = 8 := by decide
theorem a_two : a 2 = 216 := by decide
theorem a_three : a 3 = 8000 := by decide

-- Define the set of variables {x, y, z}
abbrev Vars := Fin 3

/--
The finsupp corresponding to the monomial $x^n y^n z^n$.
This is the map $\lambda i. n$. Since `Fin 3` is finite, this function is finitely supported.
We mark it noncomputable as it builds a mathematical object defined in terms of finite support.
-/
noncomputable def xyz_pow_n (n : ℕ) : Finsupp Vars ℕ :=
  Finsupp.ofSupportFinite (fun _ : Vars => n) (Set.toFinite _)

-- The polynomial ring over ℤ with 3 variables
local notation "P" => MvPolynomial Vars ℤ

/--
The polynomial $P_n(X, Y, Z) = (1 + X + Y + Z)^{2n} (1 + X + Y - Z)^n (1 + X - Y + Z)^n$.
We identify $X_0, X_1, X_2$ with $X, Y, Z$.
We mark it noncomputable due to dependencies in the polynomial ring structure.
-/
noncomputable def P_n (n : ℕ) : P :=
  let X := MvPolynomial.X 0
  let Y := MvPolynomial.X 1
  let Z := MvPolynomial.X 2
  let p1 : P := 1 + X + Y + Z
  let p2 : P := 1 + X + Y - Z
  let p3 : P := 1 + X - Y + Z
  p1 ^ (2 * n) * p2 ^ n * p3 ^ n

/--
**oeis_2897_conjecture_0**:
Conjecture: The g.f. is also the diagonal of the rational function 1/(1 - (x + y)*(1 - 4*z*t) - z - t) = 1/det(I - M*diag(x, y, z, t)), I the 4 x 4 unit matrix and M the 4 x 4 matrix [1, 1, 1, 1; 1, 1, 1, 1; 1, 1, 1, -1; 1 , 1, -1, 1]. If true, then a(n) = [(x*y*z)^n] (1 + x + y + z)^(2*n)*(1 + x + y - z)^n*(1 + x - y + z)^n. - _Peter Bala_, Apr 10 2022
-/
theorem oeis_2897_conjecture_0 (n : ℕ) :
  (a n : ℤ) = MvPolynomial.coeff (xyz_pow_n n) (P_n n) :=
by sorry
