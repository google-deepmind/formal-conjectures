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
$p_k(x) = \frac{(k-2)x(x-1)}{2} + x$ is the $x$-th $k$-gonal number.
-/
def polygonal_number (k : ℕ) (x : ℕ) : ℕ :=
  (k - 2) * (x * (x - 1) / 2) + x

/--
$p_5(y) = \frac{3y^2 - y}{2}$ is the $y$-th pentagonal number.
-/
def pentagonal (y : ℕ) : ℕ := polygonal_number 5 y

/--
$p_6(z) = 2z^2 - z$ is the $z$-th hexagonal number.
-/
def hexagonal (z : ℕ) : ℕ := polygonal_number 6 z

@[simp]
theorem pentagonal_eq_given_def (y : ℕ) : pentagonal y = (3 * y ^ 2 - y) / 2 := by
  simp only [pentagonal, polygonal_number]
  sorry -- This lemma would require careful definition of `a * (x * (x - 1) / 2) + x` for Nat division

@[simp]
theorem hexagonal_eq_given_def (z : ℕ) : hexagonal z = 2 * z ^ 2 - z := by
  simp only [hexagonal, polygonal_number]
  sorry

/--
A160324: Number of ways to express $n$ as the sum of a square, a pentagonal number and a hexagonal number.
$$a(n) = \left| \left\{(x, y, z) \in \mathbb{N}^3 : x^2 + p_5(y) + p_6(z) = n \right\} \right|$$
-/
def a (n : ℕ) : ℕ :=
  let P5 := pentagonal
  let P6 := hexagonal
  -- A practical upper bound for $x, y, z$ is $\lfloor\sqrt{n}\rfloor + 2$.
  -- Since $p_6(z) \approx 2z^2$, $z$ is bounded by approximately $\sqrt{n/2}$.
  let max_coord_bound := n.sqrt + 2

  (Finset.range max_coord_bound).sum fun x =>
  (Finset.range max_coord_bound).sum fun y =>
  (Finset.range max_coord_bound).sum fun z =>
    if x^2 + P5 y + P6 z = n then 1 else 0


theorem a_zero : a 0 = 1 := by
  sorry

theorem a_one : a 1 = 3 := by
  sorry

theorem a_two : a 2 = 3 := by
  sorry

theorem a_three : a 3 = 1 := by
  sorry

/--
%C A160324 On Aug 12 2009, _Zhi-Wei Sun_ made the following general conjecture on diagonal representations by polygonal numbers: For each integer m>2, any natural number n can be written in the form p_{m+1}(x_1)+...+p_{2m}(x_m) with x_1,...,x_m nonnegative integers, where p_k(x)=(k-2)x(x-1)/2+x (x=0,1,2,...) are k-gonal numbers.
-/
theorem oeis_a160324_conjecture_1 (m : ℕ) (hm : m > 2) (n : ℕ) :
  ∃ (x : Fin m → ℕ), n = Finset.sum Finset.univ (fun i : Fin m => polygonal_number (m + (i : ℕ) + 1) (x i)) := by
  sorry
