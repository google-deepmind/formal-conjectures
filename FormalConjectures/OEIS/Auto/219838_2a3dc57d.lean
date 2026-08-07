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
A219838: Number of ways to write $n$ as $x + y$ with $0 < x \le y$ and $(xy)^2 + xy + 1$ prime.
The constraints $x+y=n$, $0 < x \le y$ are equivalent to $1 \le x \le n/2$.
-/
def a (n : ℕ) : ℕ :=
  (Icc 1 (n / 2)).sum fun x : ℕ =>
    let xy_prod := x * (n - x)
    if Nat.Prime (xy_prod ^ 2 + xy_prod + 1) then 1 else 0

/--
Conjecture: a(n) > 0 for all n > 1.
-/
theorem oeis_219838_conjecture_0 : ∀ (n : ℕ), n > 1 → a n > 0 := by
  sorry
