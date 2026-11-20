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
Erdős Problem 634

*References:*
- [erdosproblems.com/634](https://www.erdosproblems.com/634)
-/

@[expose] public section

namespace Erdos634

abbrev Triangle := Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))

namespace Triangle

/--
Two triangles are called interior disjoint, if their interiors (as sets) are disjoint.
-/
def InteriorDisjoint (t₁ t₂ : Triangle) : Prop :=
  t₁.interior ∩ t₂.interior = ∅

/--
Two triangles are called congruent, if the lengths of their edges are equal.
-/
def Congruent (t₁ t₂ : Triangle) : Prop :=
  ({dist (t₁.points 0) (t₁.points 1), dist (t₁.points 1) (t₁.points 2),
    dist (t₁.points 2) (t₁.points 0)} : Multiset ℝ) =
  ({dist (t₂.points 0) (t₂.points 1), dist (t₂.points 1) (t₂.points 2),
    dist (t₂.points 2) (t₂.points 0)} : Multiset ℝ)

/--
Checks whether a triangle t is covered by a collection of triangles C
-/
def IsCoveredBy (t : Triangle) (C : Finset Triangle) : Prop :=
  (⋃ c ∈ C, c.closedInterior) = t.closedInterior

/--
Condition from Erdős Problem 634, `n` is congruent_triangle tileable, if
there exists a triangle which can be cut into `n` congruent triangles.
-/
def IsCongruentTriangleTileable (n : ℕ) : Prop :=
  ∃ t : Triangle,
    ∃ C : Finset Triangle,
      C.card = n ∧
      (∀ t₁ t₂ : C, t₁ ≠ t₂ → InteriorDisjoint t₁ t₂) ∧
      (∀ t₁ t₂ : C, Congruent t₁ t₂) ∧
      IsCoveredBy t C

end Triangle

def erdos_634.answer : Set ℕ := sorry

/--
Find all positive integers `n` such that
there exists a triangle that can be cut into `n` congruent triangles.
-/
@[category research open, question value, AMS 52]
theorem erdos_634 : erdos_634.answer = {n : ℕ | Triangle.IsCongruentTriangleTileable n} := by
  sorry

end Erdos634
