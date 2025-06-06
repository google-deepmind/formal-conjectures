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

/-!
# Open questions on existence of some Euler brick

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Euler_brick)
-/

/--
**Euler brick** is a rectangular cuboid whose edges and face diagonals all have integer lengths.
-/
def IsEulerBrick (a b c : ℕ+) : Prop :=
  ∃ (n m k : ℕ+), a^2 + b^2 = n^2 ∧ a^2 + c^2 = m^2 ∧ b^2 + c^2 = k^2

/--
Is there a perfect Euler brick with integer diagonal?
-/
@[category research open, AMS 11]
theorem perfect_euler_brick_existence :
    (∃ (a b c d : ℕ+), IsEulerBrick a b c ∧ a^2 + b^2 + c^2 = d^2)  ↔ answer(sorry) := by
  sorry

/--
Euler hyperbrick generalization for n-dimensional space.
-/
def IsEulerHyperBrick (n : ℕ) (edges : Fin n → ℕ+) : Prop :=
  ∀ (i j : Fin n), i < j → ∃ (k : ℕ+), (edges i)^2 + (edges j)^2 = k^2

/--
Is there a Euler brick in 4 dimentions?
-/
@[category research open, AMS 11]
theorem four_dim_euler_brick_existence :
    (∃ (edges : Fin 4 → ℕ+), IsEulerHyperBrick 4 edges)  ↔ answer(sorry) := by
  sorry

/--
Is there a Euler brick in $n>3$ dimentions?
-/
@[category research open, AMS 11]
theorem n_dim_euler_brick_existence (n : ℕ) (hn : 3 < n) :
    (∃ (edges : Fin n → ℕ+), IsEulerHyperBrick n edges)  ↔ answer(sorry) := by
  sorry
