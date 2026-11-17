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

*Reference:* [erdosproblems.com/634](https://www.erdosproblems.com/634)
-/

@[expose] public section

namespace Erdos634


abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Triangle := Affine.Triangle ℝ Plane

def triangle_interior_disjoint (t₁ t₂ : Triangle) : Prop :=
  t₁.interior ∩ t₂.interior = ∅

def triangle_congruent (t₁ t₂ : Triangle) : Prop :=
  let A : Multiset ℝ :=
    {dist (t₁.points 0) (t₁.points 1), dist (t₁.points 1) (t₁.points 2),
     dist (t₁.points 2) (t₁.points 0)}
  let B : Multiset ℝ :=
    {dist (t₂.points 0) (t₂.points 1), dist (t₂.points 1) (t₂.points 2),
     dist (t₂.points 2) (t₂.points 0)}
  A = B

def triangle_cover (t : Triangle)
    (C : Finset (Affine.Triangle ℝ Plane)) : Prop :=
  (⋃ c ∈ C, c.closedInterior) = t.closedInterior

/-
Condition from Erdős Problem 634,
'n' is congruent_triangle tileable, if
there exists a triagle which can be cut into 'n' congruent triangles.
-/
def congruent_triangle_tileable (n : ℕ) : Prop :=
  ∃ t : Triangle,
  ∃ C : Finset Triangle,
  C.card = n ∧
  (∀ t₁ t₂ : C, t₁≠ t₂ → triangle_interior_disjoint t₁ t₂ ∧ triangle_congruent t₁ t₂) ∧
  triangle_cover t C


def erdos_634.answer : Set ℕ := sorry

/--
Find all positive integers 'n' such that there exists a triangle which can be cut into 'n' congruent triangles.
-/
@[category research open, question value, AMS 52]
theorem erdos_634 :
    erdos_634.answer = {n : ℕ | congruent_triangle_tileable n} := by
  sorry

end Erdos634
