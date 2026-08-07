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

-- The provided Lean code for the sequence definition is replicated here.
/--
A379732: Decimal expansion of $207/208$.
The $n$-th term of the sequence (for $n \ge 0$) is the $(n+1)$-th digit of $207/208$
after the decimal point.
The $k$-th digit after the decimal point (for $k \ge 1$) is $\lfloor 10^k x \rfloor \pmod{10}$.
Since the OEIS sequence is 0-indexed, $a(n)$ is the $(n+1)$-th digit, $k=n+1$.
-/
def a (n : ℕ) : ℕ :=
  let p := 207
  let q := 208
  let power_of_10 := 10 ^ (n + 1)
  -- The expression calculates $\lfloor \frac{p \cdot 10^{n+1}}{q} \rfloor \pmod{10}$
  let I := (p * power_of_10) / q
  I % 10

-- We must introduce a constant for the geometric quantity being conjectured.
-- Since the concept of "densest packing of truncated tetrahedra" is not in Mathlib,
-- we introduce an `opaque` constant to represent the maximum packing density $\eta_{\max}$.
-- For formalization purposes, we give it a type `Real`.
opaque max_packing_density_truncated_tetrahedra : Real

/--
A379732 Conjectured densest packing of truncated tetrahedra.
The maximum packing density $\eta_{\max}$ of congruent truncated tetrahedra in 3D Euclidean space
is conjectured to be $207/208$.
-/
theorem oeis_379732_conjecture_0 : max_packing_density_truncated_tetrahedra = (207 : Real) / 208 :=
by sorry
