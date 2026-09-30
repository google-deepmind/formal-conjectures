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
import Mathlib

/-!
# Erdős Problem 173

-/

namespace Erdos173

/-- The genuine Euclidean plane, with its Euclidean distance. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A labelled nondegenerate triangle. Labels are ignored by congruence. -/
structure Triangle where
  vertex : Fin 3 → Plane
  nondegenerate : AffineIndependent ℝ vertex

/-- An arbitrary colouring using at most two colours. -/
abbrev Colouring := Plane → Fin 2

/-- Euclidean congruence up to relabelling of the three vertices.
For triangles, equality of all pairwise distances is the SSS criterion. -/
def Congruent (T U : Triangle) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3), ∀ i j : Fin 3,
    dist (T.vertex i) (T.vertex j) =
      dist (U.vertex (σ i)) (U.vertex (σ j))

/-- All three vertices have the same colour. -/
def Monochromatic (c : Colouring) (T : Triangle) : Prop :=
  ∀ i j : Fin 3, c (T.vertex i) = c (T.vertex j)

/-- Some triangle congruent to T has three vertices of one colour. -/
def HasMonochromaticCopy (c : Colouring) (T : Triangle) : Prop :=
  ∃ U : Triangle, Congruent T U ∧ Monochromatic c U

/-- Erdős Problem 173: the exceptional triangles, if any, belong to at
most one congruence class. The exceptional class may depend on c. -/
def Conjecture : Prop :=
  ∀ c : Colouring, ∀ T U : Triangle,
    ¬ HasMonochromaticCopy c T →
    ¬ HasMonochromaticCopy c U →
    Congruent T U

/-- Equivalent formulation: of any two noncongruent triangles, at least
one has a monochromatic congruent copy in the given colouring. -/
def PairFormulation : Prop :=
  ∀ c : Colouring, ∀ T U : Triangle,
    ¬ Congruent T U →
    HasMonochromaticCopy c T ∨ HasMonochromaticCopy c U

/-! Elementary supporting proofs; none proves the open conjecture. -/

theorem congruent_refl (T : Triangle) : Congruent T T := by
  refine ⟨Equiv.refl (Fin 3), ?_⟩
  intro i j
  rfl

theorem congruent_symm {T U : Triangle}
    (h : Congruent T U) : Congruent U T := by
  rcases h with ⟨σ, hσ⟩
  refine ⟨σ.symm, ?_⟩
  intro i j
  simpa using (hσ (σ.symm i) (σ.symm j)).symm

theorem congruent_trans {T U V : Triangle}
    (hTU : Congruent T U) (hUV : Congruent U V) : Congruent T V := by
  rcases hTU with ⟨σ, hσ⟩
  rcases hUV with ⟨τ, hτ⟩
  refine ⟨σ.trans τ, ?_⟩
  intro i j
  exact (hσ i j).trans (hτ (σ i) (σ j))

/-- A monochromatic triangle is itself a suitable copy. -/
theorem hasCopy_of_monochromatic {c : Colouring} {T : Triangle}
    (h : Monochromatic c T) : HasMonochromaticCopy c T := by
  exact ⟨T, congruent_refl T, h⟩

/-- The existence of a copy depends only on the congruence class. -/
theorem hasCopy_iff_of_congruent {c : Colouring} {T U : Triangle}
    (h : Congruent T U) :
    HasMonochromaticCopy c T ↔ HasMonochromaticCopy c U := by
  constructor
  · rintro ⟨V, hTV, hV⟩
    exact ⟨V, congruent_trans (congruent_symm h) hTV, hV⟩
  · rintro ⟨V, hUV, hV⟩
    exact ⟨V, congruent_trans h hUV, hV⟩

/-- The two formulations of the question are logically equivalent. -/
theorem conjecture_iff_pairFormulation : Conjecture ↔ PairFormulation := by
  classical
  constructor
  · intro h c T U hnoncongruent
    by_cases hT : HasMonochromaticCopy c T
    · exact Or.inl hT
    · by_cases hU : HasMonochromaticCopy c U
      · exact Or.inr hU
      · exact False.elim (hnoncongruent (h c T U hT hU))
  · intro h c T U hT hU
    by_contra hnoncongruent
    rcases h c T U hnoncongruent with hcopy | hcopy
    · exact hT hcopy
    · exact hU hcopy

end Erdos173
