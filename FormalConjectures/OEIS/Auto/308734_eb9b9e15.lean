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

open Nat Finset

/--
A308734: Number of ordered ways to write $n$ as $(2^a \cdot 3^b)^2 + (2^c \cdot 5^d)^2 + x^2 + y^2$,
where $a,b,c,d,x,y$ are nonnegative integers with $x \le y$.

Note: The provided definition uses a computationally convenient, but potentially insufficient, range `M` for the exponents $a, b, c, d$.
A mathematically precise definition would use unbounded natural numbers for $a, b, c, d, x, y$ and count the size of the resulting set.
We proceed with the definition as given in the prompt.
-/
def A308734 (n : ℕ) : ℕ :=
  -- We use a six-fold nested summation over a range $M$.
  let M := Nat.sqrt n + 1

  Finset.sum (range M) fun a =>
  Finset.sum (range M) fun b =>
  Finset.sum (range M) fun c =>
  Finset.sum (range M) fun d =>
  Finset.sum (range M) fun x =>
  Finset.sum (range M) fun y =>
    let term1 := (2^a * 3^b)^2
    let term2 := (2^c * 5^d)^2

    if term1 + term2 + x^2 + y^2 = n ∧ x ≤ y
    then 1
    else 0

/--
Four-square Conjecture: a(n) > 0 for all n > 1.
This is much stronger than Lagrange's four-square theorem.
(OEIS A308734, Comment C2)
-/
theorem oeis_a308734_conjecture_0 : ∀ n : ℕ, 1 < n → A308734 n > 0 := by
  sorry
