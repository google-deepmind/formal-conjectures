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
A113258: Ascending descending base exponent transform of factorials.
$$a(n) = \sum_{i = 1}^n (i!) ^ {(n-i+1)!}$$
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) fun i => (Nat.factorial (i + 1)) ^ (Nat.factorial (n - i))


theorem a_one : a 1 = 1 := by
  delta a
  rfl

theorem a_two : a 2 = 3 := by
  delta a
  rfl

theorem a_three : a 3 = 11 := by
  delta a
  rfl

theorem a_four : a 4 = 125 := by
  delta a
  rfl

/--
Is there a nontrivial power after a(4) = 5^3? That is, does there exist an $n > 4$
such that $a(n)$ is a perfect power with base $> 1$ and exponent $> 1$?
-/
theorem oeis_a113258_conjecture_0 :
  ∃ (n : ℕ), 4 < n ∧ ∃ (b e : ℕ), 1 < b ∧ 1 < e ∧ a n = b ^ e := by
  sorry
