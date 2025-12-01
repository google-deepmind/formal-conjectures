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
# Erdős Problem 774

*Reference:* [erdosproblems.com/774](https://www.erdosproblems.com/774)

We call `A ⊂ ℕ` **dissociated** if
∑ n ∈ X n ≠ ∑ m ∈ Y m
for all finite `X, Y ⊂ A` with `X ≠ Y`.

Let `A ⊂ ℕ` be an infinite set.
We call `A` **proportionately dissociated** if every finite `B ⊂ A` contains
a dissociated set of size ≫ |B|.

**Conjecture (open):**
Is every proportionately dissociated set the union of finitely many dissociated sets?
-/

namespace Erdos774

open Set
open scoped BigOperators


<<<<<<< HEAD
def IsPropDissociated (A : Set ℕ) : Prop :=
  ∀ (B : Finset ℕ), (∀ b ∈ B, b ∈ A) →
    ∃ (D : Finset ℕ),
      D ⊆ B ∧
      AddDissociated (↑D : Set ℕ) ∧
      (D.card ≫ B.card)
=======
/-- An infinite set `A` is proportionately dissociated if every finite subset
contains a large dissociated subset. -/
def IsPropDissociated (A : Set ℕ) : Prop :=
  ∀ (B : Finset ℕ), (∀ b ∈ B, b ∈ A) →
    ∃ (D : Finset ℕ), D ⊆ B ∧ IsDissociated D ∧ (D.card ≫ B.card)
>>>>>>> 8070d4e155d2c3867a38681ebbe87f6de0f701ca

/--
**Erdős Problem 774**

Is every proportionately dissociated set the union of finitely many dissociated sets?
-/
@[category research open, AMS 11]
theorem erdos_774_statement :
    (∀ A : Set ℕ, IsPropDissociated A →
      ∃ (k : ℕ) (A₁ … Aₖ : Set ℕ),
<<<<<<< HEAD
        (∀ i, AddDissociated (Aᵢ : Set ℕ)) ∧ A = ⋃ i, Aᵢ) ↔ answer(sorry) := by
=======
        (∀ i, AddDissociated Aᵢ) ∧ A = ⋃ i, Aᵢ) ↔ answer(sorry) := by
>>>>>>> 8070d4e155d2c3867a38681ebbe87f6de0f701ca
  sorry

end Erdos774
