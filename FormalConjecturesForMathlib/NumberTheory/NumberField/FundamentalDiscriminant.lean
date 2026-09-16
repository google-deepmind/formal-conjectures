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
module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Int.ModEq

@[expose] public section

/-!
# Fundamental discriminants

A fundamental discriminant is an integer that occurs as the discriminant of a quadratic field.

*References:*
- [Wikipedia, Fundamental discriminant](https://en.wikipedia.org/wiki/Fundamental_discriminant)
-/

namespace NumberField

/-- Fundamental discriminants are those integers `D` that appear as discriminants of quadratic
fields.

`D` is a fundamental discriminant if it is either of the form `4m` for `m` congruent to `2` or `3`
mod `4` squarefree, or if it congruent to `1` mod `4` and squarefree. -/
def IsFundamentalDiscr (D : ℤ) : Prop :=
  4 ∣ D ∧ ¬ D / 4 ≡ 1 [ZMOD 4] ∧ Squarefree (D / 4) ∨ D ≠ 1 ∧ D ≡ 1 [ZMOD 4] ∧ Squarefree D

/-- Unfolding of `IsFundamentalDiscr` in terms of `%`: a fundamental discriminant is either
`4` times a squarefree integer congruent to `2` or `3` mod `4`, or a squarefree integer
congruent to `1` mod `4` other than `1` itself. -/
theorem isFundamentalDiscr_iff {D : ℤ} :
    IsFundamentalDiscr D ↔
      (∃ m, D = 4 * m ∧ (m % 4 = 2 ∨ m % 4 = 3) ∧ Squarefree m) ∨
        D ≠ 1 ∧ D % 4 = 1 ∧ Squarefree D := by
  have hsq {m : ℤ} (hm : Squarefree m) : ¬ (4 : ℤ) ∣ m := fun ⟨c, hc⟩ =>
    absurd (hm 2 ⟨c, by omega⟩) (by simp [Int.isUnit_iff])
  simp only [IsFundamentalDiscr, Int.ModEq]
  norm_num
  constructor
  · rintro (⟨⟨m, rfl⟩, hm₄, hm⟩ | h)
    · rw [Int.mul_ediv_cancel_left _ (by norm_num)] at hm₄ hm
      exact .inl ⟨m, rfl, by have := hsq hm; omega, hm⟩
    · exact .inr h
  · rintro (⟨m, rfl, hm₄, hm⟩ | h)
    · rw [Int.mul_ediv_cancel_left _ (by norm_num)]
      exact .inl ⟨⟨m, rfl⟩, by omega, hm⟩
    · exact .inr h

end NumberField
