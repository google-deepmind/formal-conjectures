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
# Sum of three cubes

An integer `n : ℤ` can be written as a sum of three cubes (of integers) if and only if
`n` is not `4` or `5` mod `9`.

*References:*
 - [Wikipedia](https://en.wikipedia.org/wiki/Sums_of_three_cubes)
 - [mathoverflow/100324](https://mathoverflow.net/a/100324)
asked by user [*David Feldman*](https://mathoverflow.net/users/10909/david-feldman)
-/

/-- The predicate that `n : ℤ` is a sum of three (integer) cubes. -/
def IsSumOfThreeCubes (n : ℤ) : Prop :=
  ∃ x y z : ℤ, n = x^3 + y^3 + z^3

@[category test, AMS 11]
theorem isSumOfThreeCubes_2 : IsSumOfThreeCubes 2 :=
  ⟨1, 1, 0, by norm_num⟩

@[category test, AMS 11]
theorem isSumOfThreeCubes_33 : IsSumOfThreeCubes 33 :=
  ⟨8866128975287528, -8778405442862239, -2736111468807040, by norm_num⟩

@[category test, AMS 11]
theorem mod_9_of_isSumOfThreeCubes (n : ℤ) (hn : IsSumOfThreeCubes n) :
    ¬(n ≡ 4 [ZMOD 9] ∨ n ≡ 5 [ZMOD 9]) := by
  rw [show (9 : ℤ) = (9 : ℕ) from rfl, ← ZMod.intCast_eq_intCast_iff _ _ 9,
    ← ZMod.intCast_eq_intCast_iff _ _ 9]
  obtain ⟨x, y, z, hn⟩ := hn
  replace hn := congrArg (fun x : ℤ ↦ (x : ZMod 9)) hn
  simp only [Int.cast_add, Int.cast_pow] at hn
  generalize (n : ZMod 9) = n at *
  generalize (x : ZMod 9) = x at *
  generalize (y : ZMod 9) = y at *
  generalize (z : ZMod 9) = z at *
  decide +revert

/-- An integer `n : ℤ` can be written as a sum of three cubes (of integers) if and only if
`n` is not `4` or `5` mod `9`. -/
@[category research open, AMS 12]
theorem isSumOfThreeCubes_iff_mod_9 :
    (∀ n : ℤ, IsSumOfThreeCubes n ↔ ¬(n ≡ 4 [ZMOD 9] ∨ n ≡ 5 [ZMOD 9])) ↔ answer(sorry) := by
  sorry
