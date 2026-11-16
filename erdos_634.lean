import Mathlib.Geometry.Euclidean.Triangle

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
