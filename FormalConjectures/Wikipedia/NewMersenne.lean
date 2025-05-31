/-
Copyright 2025 The Formal Conjectures Authors.

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

def condition1 (p : ℕ) : Prop :=
∃ k : ℕ, p = 2^k + 1 ∨ p = 2^k - 1 ∨ p = 4^k + 3 ∨ p = 4^k - 3

def condition2 (p : ℕ) : Prop :=
  Nat.Prime (2^p - 1)

def condition3 (p : ℕ) : Prop :=
  Nat.Prime ((2^p + 1) / 3)

/-!
# New Mersenne conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Mersenne_conjectures)
-/
@[category research open, AMS 11]
theorem new_mersenne_conjecture :
  ∀ p : ℕ, Odd p →
  (
    (condition1 p ∧ condition2 p → condition3 p) ∧
    (condition1 p ∧ condition3 p → condition2 p) ∧
    (condition2 p ∧ condition3 p → condition1 p)
  ) := by
  sorry
