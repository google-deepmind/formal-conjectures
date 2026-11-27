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

public import FormalConjecturesUtil

/-!
# Prime Lucas numbers

The Lucas numbers satisfy $L_0=2$, $L_1=1$, and $L_{n+2}=L_{n+1}+L_n$.
OEIS A005479 lists their prime values. The predicate below records membership in that list.

*References:*
- [A005479](https://oeis.org/A005479)
- [A000032](https://oeis.org/A000032)
-/

@[expose] public section

namespace OeisA5479

/-- A prime that occurs as a Lucas number. -/
def A (p : ℕ) : Prop := p.Prime ∧ ∃ n, lucasNumber n = (p : ℤ)

@[category test, AMS 11]
theorem a_2 : A 2 := by
  exact ⟨by norm_num, 0, by decide⟩

@[category test, AMS 11]
theorem a_3 : A 3 := by
  exact ⟨by norm_num, 2, by decide⟩

@[category test, AMS 11]
theorem a_7 : A 7 := by
  exact ⟨by norm_num, 4, by decide⟩

@[category test, AMS 11]
theorem a_11 : A 11 := by
  exact ⟨by norm_num, 5, by decide⟩

@[category test, AMS 11]
theorem a_29 : A 29 := by
  exact ⟨by norm_num, 7, by decide⟩

@[category test, AMS 11]
theorem a_47 : A 47 := by
  exact ⟨by norm_num, 8, by decide⟩

@[category test, AMS 11]
theorem a_2207 : A 2207 := by
  exact ⟨by norm_num, 16, by decide⟩

@[category test, AMS 11]
theorem a_0 : ¬ A 0 := by
  norm_num [A]

@[category test, AMS 11]
theorem a_1 : ¬ A 1 := by
  norm_num [A]

@[category test, AMS 11]
theorem a_4 : ¬ A 4 := by
  norm_num [A]

@[category test, AMS 11]
theorem lucas_number_zero : lucasNumber 0 = 2 := rfl

@[category test, AMS 11]
theorem lucas_number_one : lucasNumber 1 = 1 := rfl

@[category test, AMS 11]
theorem lucas_number_add_two (n : ℕ) :
    lucasNumber (n + 2) = lucasNumber (n + 1) + lucasNumber n := by
  simp [lucasNumber, LucasSequence.V]

/--
"Conjectures: $7$, $47$ and $2207$ are the only $a(n) \bmod 10 = 7$."
-/
@[category research open, AMS 11]
theorem lucas_primes_ending_in_seven :
    ∀ p, A p → p % 10 = 7 → p = 7 ∨ p = 47 ∨ p = 2207 := by
  sorry

end OeisA5479
