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

open Nat Set

/--
A247824: Least positive integer $m$ such that $m + n$ divides $\mathrm{prime}(m) + \mathrm{prime}(n)$.
Here $\mathrm{prime}(k)$ denotes the $k$-th prime number, with $\mathrm{prime}(1) = 2$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else
  sInf { m : ℕ | m > 0 ∧ (m + n) ∣ (Nat.nth Nat.Prime (m - 1) + Nat.nth Nat.Prime (n - 1)) }


theorem a_one : a 1 = 1 := by
  sorry

theorem a_two : a 2 = 5 := by
  sorry

theorem a_three : a 3 = 5 := by
  sorry

theorem a_four : a 4 = 5 := by
  sorry


/--
Conjecture: a(n) exists for any n > 0. Moreover, a(n) < n*(n-1) for all n > 2. - _Zhi-Wei Sun_, Sep 25 2014
The existence of $a(n)$ for $n > 0$ is formalized as the non-emptiness of the set used in the definition of $\mathrm{sInf}$, which guarantees a positive least element exists.
-/
theorem oeis_247824_conjecture_0 :
  (∀ n : ℕ, 0 < n →
    ({ m : ℕ | 0 < m ∧ (m + n) ∣ (Nat.nth Nat.Prime (m - 1) + Nat.nth Nat.Prime (n - 1)) }).Nonempty)
  ∧
  (∀ n : ℕ, 2 < n → a n < n * (n - 1)) :=
by sorry
