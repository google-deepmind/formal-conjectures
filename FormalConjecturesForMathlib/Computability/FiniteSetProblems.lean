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

public import FormalConjecturesForMathlib.Computability.BitstringEncoding
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Powerset

/-!
# Encoded finite-set and three-dimensional matching problems

These predicates implement Karp's set packing, set covering, exact cover, exact hitting,
and three-dimensional matching problems. See *Reducibility among Combinatorial Problems*
(1972), Main Theorem items 4, 6, 14, 15, 17, pp. 94–95,
https://doi.org/10.1007/978-1-4684-2001-2_9.

Natural-number element names use the existing binary encoding. Families are explicit
lists of rows, not succinct descriptions. Repeated names within a row denote one element.
Rows are indexed: repeated rows are separate available choices, including empty rows.
Exact cover and matching carry their ambient universe explicitly. Malformed inputs are
rejected. Exact hitting means one element per row, with no cardinality budget on the witness.

Decidability uses finite exhaustive enumeration, with no polynomial-time claim.
-/

@[expose] public section

namespace Computability.FiniteSetProblems

/-- An explicitly listed, indexed family of finite sets with binary element names. -/
abbrev Family := List (List ℕ)

/-- The set at a row index; repeated element names collapse. -/
def row (family : Family) (i : Fin family.length) : Finset ℕ :=
  family[i].toFinset

/-- Union of the rows selected by their indices. -/
def covered (family : Family) (chosen : Finset (Fin family.length)) : Finset ℕ :=
  chosen.biUnion (row family)

/-- The represented ground set, not all natural numbers below the largest name. -/
def ground (family : Family) : Finset ℕ := covered family Finset.univ

theorem row_subset_ground (family : Family) (i : Fin family.length) :
    row family i ⊆ ground family :=
  Finset.subset_biUnion_of_mem _ (Finset.mem_univ i)

/-- Selected rows are pairwise disjoint; distinct indices count as distinct choices. -/
def DisjointRows (family : Family) (chosen : Finset (Fin family.length)) : Prop :=
  ∀ i ∈ chosen, ∀ j ∈ chosen, i ≠ j → Disjoint (row family i) (row family j)

instance (family : Family) (chosen : Finset (Fin family.length)) :
    Decidable (DisjointRows family chosen) := by
  unfold DisjointRows
  infer_instance

/-- A positive requested number of pairwise disjoint rows. -/
def SetPacking (input : Family × ℕ) : Prop :=
  0 < input.2 ∧ ∃ chosen : Finset (Fin input.1.length),
    chosen.card = input.2 ∧ DisjointRows input.1 chosen

instance (input : Family × ℕ) : Decidable (SetPacking input) := by
  unfold SetPacking
  infer_instance

/-- At most the positive budget of rows covers the union of the whole family. -/
def SetCovering (input : Family × ℕ) : Prop :=
  0 < input.2 ∧ ∃ chosen : Finset (Fin input.1.length),
    chosen.card ≤ input.2 ∧ covered input.1 chosen = ground input.1

instance (input : Family × ℕ) : Decidable (SetCovering input) := by
  unfold SetCovering
  infer_instance

/-- Every represented row is contained in the explicit ambient universe. -/
def ValidFamily (carrier : List ℕ) (family : Family) : Prop :=
  ∀ i : Fin family.length, row family i ⊆ carrier.toFinset

instance (carrier : List ℕ) (family : Family) : Decidable (ValidFamily carrier family) := by
  unfold ValidFamily
  infer_instance

/-- Pairwise disjoint selected rows cover the explicit ambient universe. -/
def ExactCover (input : List ℕ × Family) : Prop :=
  ValidFamily input.1 input.2 ∧ ∃ chosen : Finset (Fin input.2.length),
    DisjointRows input.2 chosen ∧ covered input.2 chosen = input.1.toFinset

instance (input : List ℕ × Family) : Decidable (ExactCover input) := by
  unfold ExactCover
  infer_instance

/-- An exact cover also forces the union of the whole family to equal the ambient universe. -/
theorem ExactCover.ground_eq {input : List ℕ × Family} (h : ExactCover input) :
    ground input.2 = input.1.toFinset := by
  rcases h with ⟨valid, chosen, _, covers⟩
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    exact valid i hi
  · rw [← covers]
    intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    exact row_subset_ground input.2 i hi

/-- Karp's exact hitting problem: every row intersects the witness in exactly one element. -/
def ExactHitting (family : Family) : Prop :=
  ∃ chosen ⊆ ground family, ∀ i : Fin family.length, (chosen ∩ row family i).card = 1

instance (family : Family) : Decidable (ExactHitting family) := by
  unfold ExactHitting
  infer_instance

/-- Elements outside the represented ground set never affect an exact hitting witness. -/
theorem exactHitting_iff (family : Family) :
    ExactHitting family ↔
      ∃ chosen : Finset ℕ, ∀ i : Fin family.length, (chosen ∩ row family i).card = 1 := by
  constructor
  · rintro ⟨chosen, _, h⟩
    exact ⟨chosen, h⟩
  · rintro ⟨chosen, h⟩
    refine ⟨chosen ∩ ground family, Finset.inter_subset_right, fun i ↦ ?_⟩
    rw [Finset.inter_assoc, Finset.inter_eq_right.mpr (row_subset_ground family i)]
    exact h i

/-- All three coordinates use the same explicitly named finite universe. -/
abbrev Triple := ℕ × ℕ × ℕ

/-- An ambient universe and an explicitly listed ternary relation. -/
abbrev MatchingInput := List ℕ × List Triple

/-- Every listed triple belongs to the cube of the ambient universe. -/
def ValidMatching (input : MatchingInput) : Prop :=
  ∀ t ∈ input.2, t.1 ∈ input.1 ∧ t.2.1 ∈ input.1 ∧ t.2.2 ∈ input.1

instance (input : MatchingInput) : Decidable (ValidMatching input) := by
  unfold ValidMatching
  infer_instance

/-- No two distinct selected triples agree in any coordinate. -/
def CoordinateDisjoint (chosen : Finset Triple) : Prop :=
  ∀ t ∈ chosen, ∀ u ∈ chosen, t ≠ u →
    t.1 ≠ u.1 ∧ t.2.1 ≠ u.2.1 ∧ t.2.2 ≠ u.2.2

instance (chosen : Finset Triple) : Decidable (CoordinateDisjoint chosen) := by
  unfold CoordinateDisjoint
  infer_instance

/-- A matching of size exactly the cardinality of the ambient universe. -/
def ThreeDimensionalMatching (input : MatchingInput) : Prop :=
  ValidMatching input ∧ ∃ chosen ⊆ input.2.toFinset,
    chosen.card = input.1.toFinset.card ∧ CoordinateDisjoint chosen

instance (input : MatchingInput) : Decidable (ThreeDimensionalMatching input) := by
  unfold ThreeDimensionalMatching
  infer_instance

end Computability.FiniteSetProblems
