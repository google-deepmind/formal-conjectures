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

public import FormalConjecturesForMathlib.AlgebraicGeometry.SmoothLocus
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# A finite smooth decomposition of reduced closed subschemes

Each step takes the actual reduced closed subscheme on a closed subset, removes its smooth
locus, and continues on the closed remainder. Noetherian induction makes this construction
finite. The pieces are actual smooth locally closed subschemes, not supplied stratification
data. This is an algebraic prerequisite for dimension induction; it does not assert a
Whitney or frontier condition, triangulation, analytic homology vanishing, or extension of an
orientation across singularities.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

/-- The actual reduced closed subscheme on a closed subset. -/
def reducedClosedSubscheme (S : Closeds X) : Scheme :=
  (Scheme.IdealSheafData.vanishingIdeal S).subscheme

/-- The canonical inclusion of the reduced closed subscheme. -/
def reducedClosedSubschemeι (S : Closeds X) : reducedClosedSubscheme S ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal S).subschemeι

instance reducedClosedSubschemeι_isClosedImmersion (S : Closeds X) :
    IsClosedImmersion (reducedClosedSubschemeι S) := by
  change IsClosedImmersion (Scheme.IdealSheafData.vanishingIdeal S).subschemeι
  infer_instance

instance reducedClosedSubscheme_isReduced (S : Closeds X) :
    IsReduced (reducedClosedSubscheme S) := by
  let I := Scheme.IdealSheafData.vanishingIdeal S
  change IsReduced I.subscheme
  rw [IsReduced.iff_of_openCover I.subscheme I.subschemeCover.openCover]
  intro U
  let U' : X.affineOpens := U
  change IsReduced (Spec (.of (Γ(X, U') ⧸ I.ideal U')))
  rw [affine_isReduced_iff, ← Ideal.isRadical_iff_quotient_reduced]
  exact PrimeSpectrum.isRadical_vanishingIdeal _

@[simp] lemma range_reducedClosedSubschemeι (S : Closeds X) :
    Set.range (reducedClosedSubschemeι S) = (S : Set X) :=
  Scheme.IdealSheafData.range_subschemeι _

variable {K : Type u} [Field K]
  (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]

/-- The structure morphism of the actual reduced closed subscheme. -/
def reducedClosedStructureMap (S : Closeds X) :
    reducedClosedSubscheme S ⟶ Spec (.of K) :=
  reducedClosedSubschemeι S ≫ f

instance reducedClosedStructureMap_locallyOfFiniteType (S : Closeds X) :
    LocallyOfFiniteType (reducedClosedStructureMap f S) := by
  dsimp [reducedClosedStructureMap]
  infer_instance

/-- The smooth piece removed from a closed subset at one step. -/
def reducedClosedSmoothPiece (S : Closeds X) : Scheme :=
  (reducedClosedStructureMap f S).smoothLocus

/-- This piece is locally closed in the original ambient scheme. -/
def reducedClosedSmoothPieceι (S : Closeds X) : reducedClosedSmoothPiece f S ⟶ X :=
  (reducedClosedStructureMap f S).smoothLocus.ι ≫ reducedClosedSubschemeι S

set_option backward.isDefEq.respectTransparency false in
instance reducedClosedSmoothPieceι_isImmersion (S : Closeds X) :
    IsImmersion (reducedClosedSmoothPieceι f S) := by
  change IsImmersion
    ((reducedClosedStructureMap f S).smoothLocus.ι ≫ reducedClosedSubschemeι S)
  infer_instance

instance reducedClosedSmoothPiece_smooth (S : Closeds X) :
    Smooth (reducedClosedSmoothPieceι f S ≫ f) := by
  change Smooth ((reducedClosedStructureMap f S).smoothLocus.ι ≫
    reducedClosedSubschemeι S ≫ f)
  exact (reducedClosedStructureMap f S).smooth_restrict_smoothLocus

/-- The singular remainder, regarded as a closed subset of the original scheme. -/
def reducedClosedSingularRemainder (S : Closeds X) : Closeds X :=
  ⟨reducedClosedSubschemeι S ''
    ((reducedClosedStructureMap f S).smoothLocus : Set (reducedClosedSubscheme S))ᶜ,
    (reducedClosedSubschemeι S).isClosedEmbedding.isClosedMap _
      (reducedClosedStructureMap f S).smoothLocus.isOpen.isClosed_compl⟩

lemma reducedClosedSingularRemainder_le (S : Closeds X) :
    reducedClosedSingularRemainder f S ≤ S := by
  rintro _ ⟨x, _, rfl⟩
  exact (range_reducedClosedSubschemeι S).le ⟨x, rfl⟩

lemma reducedClosedSingularRemainder_lt [PerfectField K] (S : Closeds X) (hS : S ≠ ⊥) :
    reducedClosedSingularRemainder f S < S := by
  refine lt_of_le_of_ne (reducedClosedSingularRemainder_le f S) ?_
  have hne : Nonempty (reducedClosedSubscheme S) := by
    obtain ⟨x, hx⟩ := Closeds.coe_nonempty.mpr hS
    obtain ⟨y, _⟩ := (range_reducedClosedSubschemeι S).ge hx
    exact ⟨y⟩
  obtain ⟨x, hx⟩ :=
    (reducedClosedStructureMap f S).dense_smoothLocus_of_perfectField.nonempty
  intro h
  have hmem : reducedClosedSubschemeι S x ∈ reducedClosedSingularRemainder f S := by
    rw [h]
    exact (range_reducedClosedSubschemeι S).le ⟨x, rfl⟩
  obtain ⟨y, hy, hxy⟩ := hmem
  exact hy ((reducedClosedSubschemeι S).isClosedEmbedding.injective hxy ▸ hx)

lemma reducedClosedSmoothPiece_range (S : Closeds X) :
    Set.range (reducedClosedSmoothPieceι f S) =
      (S : Set X) \ (reducedClosedSingularRemainder f S : Set X) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨(range_reducedClosedSubschemeι S).le ⟨y.1, rfl⟩, ?_⟩
    rintro ⟨z, hz, he⟩
    exact hz ((reducedClosedSubschemeι S).isClosedEmbedding.injective he ▸ y.2)
  · rintro ⟨hx, hnot⟩
    obtain ⟨y, rfl⟩ := (range_reducedClosedSubschemeι S).ge hx
    have hy : y ∈ (reducedClosedStructureMap f S).smoothLocus := by
      by_contra hn
      exact hnot ⟨y, hn, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

local instance reducedSmoothStratificationWellFoundedRelation [NoetherianSpace X] :
    WellFoundedRelation (Closeds X) :=
  ⟨(· < ·), wellFounded_lt⟩

/-- The finite, explicitly recursive sequence of nonempty closed remainders. The actual
smooth strata are `reducedClosedSmoothPiece f S` for the members of this list. -/
def reducedSmoothStratification [PerfectField K] [NoetherianSpace X]
    (S : Closeds X) : List (Closeds X) := by
  classical
  exact if hS : S = ⊥ then []
    else S :: reducedSmoothStratification (reducedClosedSingularRemainder f S)
termination_by S
decreasing_by exact reducedClosedSingularRemainder_lt f S hS

variable [PerfectField K] [NoetherianSpace X]

lemma reducedSmoothStratification_mem_le (S T : Closeds X)
    (hT : T ∈ reducedSmoothStratification f S) : T ≤ S := by
  induction S using (wellFounded_lt (α := Closeds X)).induction with
  | h S ih =>
    rw [reducedSmoothStratification] at hT
    split_ifs at hT with hS
    · simp at hT
    · rcases List.mem_cons.mp hT with rfl | hT
      · exact le_rfl
      · exact (ih _ (reducedClosedSingularRemainder_lt f S hS) hT).trans
          (reducedClosedSingularRemainder_le f S)

lemma reducedSmoothStratification_mem_ne_bot (S T : Closeds X)
    (hT : T ∈ reducedSmoothStratification f S) : T ≠ ⊥ := by
  induction S using (wellFounded_lt (α := Closeds X)).induction with
  | h S ih =>
    rw [reducedSmoothStratification] at hT
    split_ifs at hT with hS
    · simp at hT
    · rcases List.mem_cons.mp hT with rfl | hT
      · exact hS
      · exact ih _ (reducedClosedSingularRemainder_lt f S hS) hT

/-- The actual smooth strata cover exactly the given closed set. -/
theorem reducedSmoothStratification_covers (S : Closeds X) (x : X) :
    (∃ T ∈ reducedSmoothStratification f S,
      x ∈ Set.range (reducedClosedSmoothPieceι f T)) ↔ x ∈ S := by
  induction S using (wellFounded_lt (α := Closeds X)).induction with
  | h S ih =>
    rw [reducedSmoothStratification]
    split_ifs with hS
    · simp only [List.not_mem_nil, false_and, exists_false]
      subst S
      rfl
    · simp only [List.mem_cons, or_and_right, exists_or, exists_eq_left]
      rw [ih _ (reducedClosedSingularRemainder_lt f S hS), reducedClosedSmoothPiece_range]
      exact ⟨fun h => h.elim And.left (fun hx => reducedClosedSingularRemainder_le f S hx),
        fun hx => by
          by_cases hmem : x ∈ reducedClosedSingularRemainder f S
          · exact Or.inr hmem
          · exact Or.inl ⟨hx, hmem⟩⟩

/-- The locally closed smooth strata are pairwise disjoint. -/
theorem reducedSmoothStratification_pairwiseDisjoint (S : Closeds X) :
    (reducedSmoothStratification f S).Pairwise
      (fun T U => Disjoint (Set.range (reducedClosedSmoothPieceι f T))
        (Set.range (reducedClosedSmoothPieceι f U))) := by
  induction S using (wellFounded_lt (α := Closeds X)).induction with
  | h S ih =>
    rw [reducedSmoothStratification]
    split_ifs with hS
    · exact .nil
    · rw [List.pairwise_cons]
      refine ⟨fun T hT => ?_, ih _ (reducedClosedSingularRemainder_lt f S hS)⟩
      rw [Set.disjoint_left]
      intro x hxS hxT
      have hx := (reducedSmoothStratification_covers f _ x).mp ⟨T, hT, hxT⟩
      rw [reducedClosedSmoothPiece_range] at hxS
      exact hxS.2 hx

/-- Every stratum in the constructed list is nonempty. In particular the recursion does
not insert empty smooth schemes as padding. -/
theorem reducedSmoothStratification_piece_nonempty (S T : Closeds X)
    (hT : T ∈ reducedSmoothStratification f S) :
    Nonempty (reducedClosedSmoothPiece f T) := by
  have hlt := reducedClosedSingularRemainder_lt f T
    (reducedSmoothStratification_mem_ne_bot f S T hT)
  obtain ⟨x, hxT, hxnot⟩ := Set.exists_of_ssubset hlt
  obtain ⟨y, _⟩ := (reducedClosedSmoothPiece_range f T).ge ⟨hxT, hxnot⟩
  exact ⟨y⟩

/-- The supporting closed subsets form a strictly descending finite filtration. -/
theorem reducedSmoothStratification_pairwise_gt (S : Closeds X) :
    (reducedSmoothStratification f S).Pairwise (fun T U => U < T) := by
  induction S using (wellFounded_lt (α := Closeds X)).induction with
  | h S ih =>
    rw [reducedSmoothStratification]
    split_ifs with hS
    · exact .nil
    · rw [List.pairwise_cons]
      exact ⟨fun T hT =>
        (reducedSmoothStratification_mem_le f _ T hT).trans_lt
          (reducedClosedSingularRemainder_lt f S hS),
        ih _ (reducedClosedSingularRemainder_lt f S hS)⟩

end AlgebraicGeometry
