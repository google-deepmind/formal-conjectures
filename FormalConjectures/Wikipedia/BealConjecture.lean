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
# Beal conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Beal_conjecture)
-/

namespace BealConjecture

def BealConjecture : Prop := ∀ {A B C x y z : ℕ},
    A ≠ 0 → B ≠ 0 → C ≠ 0 → 2 < x → 2 < y → 2 < z →
    A^x + B^y = C^z → 1 < Finset.gcd {A, B, C} id

/--
The **Beal Conjecture**: if we are given positive integers $A, B, C, x, y, z$ such that
$x, y, z > 2$ and $A^x + B^y = C^z$ then $A, B, C$ have a common divisor.
-/
@[category research open, AMS 11]
theorem beal_conjecture : BealConjecture := by
  sorry

/--
The Beal Conjecture implies Fermat's last theorem
-/
@[category high_school, AMS 11]
theorem flt_of_beal_conjecture (H : BealConjecture) :
    FermatLastTheorem := by
  intro n hn x y z hx hy hz
  by_contra h
  apply mul_ne_zero (mul_ne_zero hx hy) hz
  by_contra H''
  obtain ⟨hx, hy, hz⟩ : x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 := by aesop
  set G := Finset.gcd {x, y, z} id
  set x' := (x / G : ℕ)
  set y' := (y / G : ℕ)
  set z' := (z / G : ℕ)
  obtain ⟨hGx, hGy, hGz⟩ : G ∣ x ∧ G ∣ y ∧ G ∣ z := by
    refine ⟨?_, ?_, ?_⟩ <;> apply Finset.gcd_dvd (by aesop)
  obtain ⟨hx', hy', hz'⟩ : x' ≠ 0 ∧ y' ≠ 0 ∧ z' ≠ 0 := by
    refine ⟨?_, ?_, ?_⟩ <;>
      apply Nat.div_ne_zero_iff_of_dvd (by assumption) |>.mpr ⟨(by assumption), _⟩ <;> aesop
  have Hxyz' : x'^n + y'^n = z'^n := by
    rwa [Nat.div_pow hGx, Nat.div_pow hGy, Nat.div_pow hGz,
      ←Nat.add_div_of_dvd_right, Nat.div_left_inj (dvd_add _ _)]
    all_goals apply pow_dvd_pow_of_dvd ; assumption
  apply ne_of_lt <| H hx' hy' hz' hn hn hn Hxyz'
  rw [←Finset.gcd_div_id_eq_one (Finset.mem_insert_self x {y, z}) (by trivial),
    Finset.gcd_eq_gcd_image, Finset.image_insert, Finset.image_insert,
    Finset.image_singleton]

end BealConjecture
