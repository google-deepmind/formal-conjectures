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
# The exact book Ramsey number R(B₅, B₉)

*Reference:* https://doi.org/10.5281/zenodo.24559340

*Reference:* https://github.com/HITESH4577/Book-Ramsey-5-9

*Reference:* https://github.com/daniel-munro/leaps-in-bounds/pull/126

The lower bound of 29 was previously reported by Quantavane.
The matching upper bound was established in the linked formalization.
-/

@[expose] public section

namespace Book59Exact

open scoped BigOperators

def commonN {n : ℕ}
    (A : Fin n → Fin n → ℤ) (i j : Fin n) : ℤ :=
  ∑ k, A i k * A k j

def blueN {n : ℕ}
    (A : Fin n → Fin n → ℤ) (i j : Fin n) : ℤ :=
  if i = j then 0 else 1 - A i j

def RamseyProperty (n : ℕ) : Prop :=
  ∀ A : Fin n → Fin n → ℤ,
    (∀ i j, A i j = A j i) →
    (∀ i, A i i = 0) →
    (∀ i j, A i j = 0 ∨ A i j = 1) →
    (∃ i j, A i j = 1 ∧ 5 ≤ commonN A i j) ∨
    (∃ i j, i ≠ j ∧ A i j = 0 ∧
      9 ≤ commonN (blueN A) i j)

/--
The exact two-colour book Ramsey number R(B₅, B₉) is 29.
-/
@[category research solved, AMS 05,
  formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-26-000049&version=1"]
theorem book_ramsey_5_9_eq_29 :
    IsLeast {n : ℕ | RamseyProperty n} 29 := by
  sorry

end Book59Exact
