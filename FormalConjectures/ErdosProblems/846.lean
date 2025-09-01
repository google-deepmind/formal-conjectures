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
# Erdős Problem 846

*Reference:* [erdosproblems.com/846](https://www.erdosproblems.com/846)
-/
open scoped EuclideanGeometry

namespace Erdos846

def Triplewise {α : Type*} (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s → x ≠ y → y ≠ z → x ≠ z → r x y z


section Prelims
open Classical

/--We say a subset `A` of points in the plane is non-trilinear if
it contains no three points that lie on the same line.-/
def NonTrilinear (A : Set ℝ²) : Prop := ∀ᵉ (x ∈ A) (y ∈ A) (z ∈ A),
  Triplewise A (fun x y z ↦ ¬ Collinear ℝ {x, y, z})


/--We say a subset `A` of points in the plane is `ε`-non-trilinear if any subset
`B` of `A`, contains a non-trilinear subset `C` of size at least `ε|B|`.-/
def NonTrilinearFor (A : Set ℝ²) (ε : ℝ) : Prop :=
  ∀ (B : Finset ℝ²), B.toSet ⊆ A → ∃ C ⊆ B,
    ε * B.card ≤ C.card ∧ NonTrilinear A

/--We say a subset `A` of points in the plane is weakly non-trilinear if it is
a finite union of non-trilinear sets.-/
def WeaklyNonTrilinear (A : Set ℝ²) : Prop :=
  ∃ B : Finset (Set ℝ²), A = sSup B ∧ ∀ b ∈ B, NonTrilinear b

end Prelims

/--
**Erdős Problem 846**
Let `A ⊂ ℝ²` be an infinite set for which there exists some `ϵ>0` such that in any subset of `A`
of size `n` there are always at least `ϵn` with no three on a line.
Is it true that `A` is the union of a finite number of sets where no three are on a line?

In other words, prove or disprove the following statement: every infinite `ε`-non-trilinear subset of the
plane is weakly non-trilinar.
-/
@[category research open, AMS 11]
theorem erdos_846 : (∀ᵉ (A : Set ℝ²) (ε > 0), A.Infinite → NonTrilinearFor A ε →
    WeaklyNonTrilinear A) ↔ answer(sorry) := by
  sorry

end Erdos846
