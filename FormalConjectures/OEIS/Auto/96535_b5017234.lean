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

/--
A096535: $a(0) = a(1) = 1$; $a(n) = (a(n-1) + a(n-2)) \bmod n$.
-/
def A096535 : ℕ → ℕ
| 0 => 1
| 1 => 1
| n + 2 => (A096535 (n + 1) + A096535 n) % (n + 2)


theorem a_zero : A096535 0 = 1 := rfl

theorem a_one : A096535 1 = 1 := rfl

theorem a_two : A096535 2 = 0 := rfl

theorem a_three : A096535 3 = 1 := by
  -- A096535 3 = (A096535 2 + A096535 1) % 3 = (0 + 1) % 3 = 1
  rfl

/--
Conjecture (1): All numbers appear infinitely often, i.e., for every number k >= 0 and every frequency f > 0 there is an index i such that a(i) = k is the f-th occurrence of k in the sequence.
-/
theorem A096535_occurs_infinitely_often (k : ℕ) :
  ∀ (N : ℕ), ∃ (n : ℕ), n > N ∧ A096535 n = k := by sorry
