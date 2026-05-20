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

open scoped Nat.Prime

/--
A238902: $a(n) = |\{0 < k \le n: \pi(\pi(k \cdot n)) \text{ is a square}\}|$,
where $\pi(x)$ denotes the number of primes not exceeding $x$.
-/
def a (n : ℕ) : ℕ :=
  Finset.card $ (Finset.Icc 1 n).filter fun k : ℕ =>
    let m := π (π (k * n))
    m.sqrt ^ 2 = m


theorem a_one : a 1 = 1 := by
  sorry

theorem a_two : a 2 = 2 := by
  sorry

theorem a_three : a 3 = 1 := by
  sorry

theorem a_four : a 4 = 1 := by
  sorry

/--
Conjecture (i): a(n) > 0 for all n > 0.
-/
theorem oeis_a238902_conjecture_i (n : ℕ) (hn : n > 0) : a n > 0 := by
  sorry
