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
A299068: Number of pairs of factors of $n^2(n^2-1)$ which differ by $n$.
Formally, this is the number of divisors $d$ of $n^2(n^2-1)$ such that $d+n$ is also a divisor of $n^2(n^2-1)$.
-/
def A299068 (n : ℕ) : ℕ :=
  let m : ℕ := n ^ 2 * (n ^ 2 - 1)
  (m.divisors.filter (fun d => d + n ∈ m.divisors)).card

theorem a_two : A299068 2 = 3 := by
  sorry

theorem a_three : A299068 3 = 4 := by
  sorry

theorem a_four : A299068 4 = 8 := by
  sorry

theorem a_five : A299068 5 = 7 := by
  sorry

/--
oeis_299068_conjecture_0: If k in A299159 is sufficiently large, then a(12*k-2)=7.
Dickson's conjecture implies there are infinitely many such k, and thus infinitely many n with a(n)=7.
-/
theorem oeis_299068_conjecture_0 : Set.Infinite {n : ℕ | A299068 n = 7} :=
by sorry
