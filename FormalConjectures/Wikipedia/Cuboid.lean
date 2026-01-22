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

/-!
# Cuboid conjectures

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Euler_brick#Cuboid_conjectures)
-/

open Polynomial Nat

namespace Cuboid

def CuboidOneFor (a b : ℕ) : Prop :=
  Irreducible (X (R := ℤ) ^ 8 + 6 * (a ^ 2 - b ^ 2) * (X (R := ℤ) ^ 6)
    + (b ^ 4 - 4 * a ^ 2 * b ^ 2 + a ^ 4) * X (R := ℤ) ^ 4
    - 6 * a ^ 2 * b ^ 2 * (a ^ 2 - b ^2) * X (R := ℤ) ^ 4 + a ^ 4 * b ^ 4)

def CuboidOne : Prop := ∀ ⦃a b : ℕ⦄, a.Coprime b → a ≠ 0 → b ≠ 0 → a ≠ b → CuboidOneFor a b

@[category research open, AMS 12]
theorem cuboidOne : CuboidOne := by sorry

def CuboidTwoFor (a b : ℕ) : Prop :=
  Irreducible (X (R := ℤ) ^ 10 + (2 * b ^ 2 + a ^ 2) * (3 * b ^ 2 - 2 * a ^ 2) * X (R := ℤ) ^ 8
    + (b ^ 8 + 10 * a ^ 2 * b ^ 6 + 4 * a ^ 4 * b ^ 4 - 14 * a ^ 6 * b ^ 2 + a ^ 8) * X (R := ℤ) ^ 6
    - a ^ 2 * b ^ 2 * (b ^ 8 - 14 * a ^ 2 * b ^ 6 + 4 * a ^ 4 * b ^ 4 + 10 * a ^ 6 * b ^ 2 + a ^ 8)
    * X (R := ℤ) ^ 4 - a ^ 6 * b ^ 6 * (b ^ 2 + 2 * a ^ 2) * (-2 * b ^ 2 + 3 * a ^ 2)
    * X (R := ℤ) ^ 2 - b ^ 10 * a ^ 10)

def CuboidTwo : Prop := ∀ ⦃a b : ℕ⦄, a.Coprime b → a ≠ 0 → b ≠ 0 → a ≠ b → CuboidTwoFor a b

@[category research open, AMS 12]
theorem cuboidTwo : CuboidTwo := by sorry

def CuboidThreeFor (a b c : ℕ) : Prop :=
  Irreducible (X (R := ℤ) ^ 12 + (6 * c ^ 2 - 2 * a ^ 2 - 2 * b ^ 2) * X (R := ℤ) ^ 10
    + (c ^ 4 + b ^ 4 + a ^ 4 + 4 * a ^ 2 * c ^ 2 + 4 * b ^ 2 * c ^ 2 - 12 * b ^ 2 * a ^ 2
    * X (R := ℤ) ^ 8) + (6 * a ^ 4 * c ^ 2 + 6 * c ^ 2 * b ^ 4 - 8 * a ^ 2 * b ^ 2 * c ^ 2
    - 2 * c ^ 4 * a ^ 2 - 2 * c ^ 4 * b ^ 2 - 2 * a ^ 4 * b ^ 2 - 2 * b ^ 4 * a ^ 2)
    * X (R := ℤ) ^ 6 + (4 * c ^ 2 * b ^ 4 * a ^ 2 + 4 * a ^ 4 * c ^ 2 * b ^ 2
    - 12 * c ^ 4 * a ^ 2 * b ^ 2 + c ^ 4 * a ^ 4 + c ^ 4 * b ^ 4 * a ^ 4 * b ^ 4) * X (R := ℤ) ^ 4
    + (6 * a ^ 4 * c ^ 2 * b ^ 4 - 2 * c ^ 4 * a ^ 4 * b ^ 2 - 2 * c ^ 4 * a ^ 2 * b ^ 4)
    * X (R := ℤ) ^ 2 + c ^ 4 * a ^ 4 * b ^ 4)

def CuboidThree : Prop := ∀ ⦃a b c : ℕ⦄, a.Coprime b → b.Coprime c → c.Coprime a → a ≠ 0 → b ≠ 0 →
  c ≠ 0 → a ≠ b → b ≠ c → c ≠ a → b * c ≠ a ^ 2 → a * c ≠ b ^ 2 → CuboidThreeFor a b c


@[category research open, AMS 12]
theorem cuboidThree : CuboidThree := by sorry

--TODO: Formalise connection with Euler brick

end Cuboid
