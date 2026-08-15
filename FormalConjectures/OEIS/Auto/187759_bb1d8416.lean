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
A187759: Number of ways to write $n=x+y$ ($0<x<y<n$) with $6x-1, 6x+1, 6y-1$ and $6y+1$ all prime.
-/
def a (n : ℕ) : ℕ :=
  let max_x : ℕ := (n - 1) / 2
  (Icc 1 max_x).sum fun x =>
    let y : ℕ := n - x
    if Nat.Prime (6 * x - 1) ∧
       Nat.Prime (6 * x + 1) ∧
       Nat.Prime (6 * y - 1) ∧
       Nat.Prime (6 * y + 1)
    then 1 else 0

/--
A187759 Conjecture: If n>200 is not among 211, 226, 541, 701, then a(n)>0.
-/
theorem oeis_187759_conjecture_0 (n : ℕ) :
    (n > 200 ∧ n ∉ ({211, 226, 541, 701} : Finset ℕ)) → a n > 0 :=
  by sorry
