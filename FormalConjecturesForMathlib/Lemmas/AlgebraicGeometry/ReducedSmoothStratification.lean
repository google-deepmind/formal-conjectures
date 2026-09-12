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

public import FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.ReducedSmoothStratification

/-!
# A finite smooth decomposition of reduced closed subschemes

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.ReducedSmoothStratification`.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

variable {K : Type u} [Field K]
  (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]

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

attribute [local instance] reducedSmoothStratificationWellFoundedRelation

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
