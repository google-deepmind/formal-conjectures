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
A230241: Number of ways to write $n = p + q$ with $p$, $3p - 10$ and $(p-1)q - 1$ all prime, where $q$ is a positive integer.
We count the number of possible values for $p$. Since $p$ must be positive and $q = n-p$ must be positive, we restrict $p$ to the set $\{1, 2, \dots, n-1\}$.
-/
def A230241 (n : ℕ) : ℕ :=
  card $ filter (fun p =>
    Nat.Prime p ∧
    Nat.Prime (3 * p - 10) ∧
    let q := n - p
    Nat.Prime ((p - 1) * q - 1)
  ) (Finset.Icc 1 (n - 1))


theorem a_one : A230241 1 = 0 := by
  constructor

theorem a_two : A230241 2 = 0 := by
  trivial

theorem a_three : A230241 3 = 0 := by
  rfl

theorem a_four : A230241 4 = 0 := by
  constructor

/--
Conjecture: a(n) > 0 for all n > 5.
-/
theorem A230241_conjecture : ∀ n : ℕ, n > 5 → A230241 n > 0 := by
  sorry
