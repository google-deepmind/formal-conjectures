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

public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Matching
public import FormalConjecturesForMathlib.Combinatorics.TransferableUtilityMatching.MarriageTable
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset

/-!
# Finite transferable-utility allocations

A partial bipartite allocation contains disjoint pairs of individuals. It need not match
anybody. Total surplus is the sum of the selected pair surpluses; singlehood has surplus zero.
Every finite market has a maximum-surplus allocation. Aggregating the selected pairs and
unmatched individuals by observed type gives a `MarriageTable` with the population margins.

The pair representation maps to `SimpleGraph.IsEdgeMatching` in the complete bipartite graph.
This module makes no assumption about how the pair surpluses are generated.

## References

* Chiappori, Nguyen, and Salanié, [*The Econometrics of Matching with Transferable Utility:
  A Progress Report*](https://dlinh-n.github.io/f/wp/CNS12April2026.pdf), §3.2.1.
-/

@[expose] public section

open scoped BigOperators NNReal

namespace TransferableUtilityMatching

/-- A finite collection of pairs uses every individual at most once on each side. -/
def IsPartialAllocation {M W : Type*} (s : Finset (M × W)) : Prop :=
  Set.InjOn Prod.fst (s : Set (M × W)) ∧ Set.InjOn Prod.snd (s : Set (M × W))

/-- A partial bipartite allocation, allowing individuals to remain single. -/
abbrev FiniteAllocation (M W : Type*) := {s : Finset (M × W) // IsPartialAllocation s}

namespace FiniteAllocation

variable {M W : Type*}

/-- The allocation in which everybody remains single. -/
def empty : FiniteAllocation M W :=
  ⟨∅, by simp [IsPartialAllocation, Set.InjOn]⟩

instance : Inhabited (FiniteAllocation M W) := ⟨empty⟩

noncomputable section

open scoped Classical in
instance [Fintype M] [Fintype W] : Fintype (FiniteAllocation M W) := Fintype.ofFinite _

/-- The allocation consisting of one pair. -/
def singleton (m : M) (w : W) : FiniteAllocation M W :=
  ⟨{(m, w)}, by simp [IsPartialAllocation, Set.InjOn]⟩

/-- Total pair surplus; the outside option contributes zero. -/
def totalSurplus (a : FiniteAllocation M W) (v : M → W → ℝ) : ℝ :=
  ∑ p ∈ a.val, v p.1 p.2

@[simp]
lemma totalSurplus_empty (v : M → W → ℝ) : empty.totalSurplus v = 0 := by
  simp [totalSurplus, empty]

@[simp]
lemma totalSurplus_singleton (m : M) (w : W) (v : M → W → ℝ) :
    (singleton m w).totalSurplus v = v m w := by
  simp [totalSurplus, singleton]

/-- A surplus-maximizing allocation permits all feasible partial allocations as competitors. -/
def IsSurplusMaximizer (a : FiniteAllocation M W) (v : M → W → ℝ) : Prop :=
  ∀ b : FiniteAllocation M W, b.totalSurplus v ≤ a.totalSurplus v

/-- A maximum-surplus allocation exists in every finite market. -/
lemma exists_surplusMaximizer [Finite M] [Finite W] (v : M → W → ℝ) :
    ∃ a : FiniteAllocation M W, a.IsSurplusMaximizer v := by
  classical
  let := Fintype.ofFinite M
  let := Fintype.ofFinite W
  obtain ⟨a, _, ha⟩ := Finset.univ.exists_max_image (fun a ↦ a.totalSurplus v)
    ⟨empty, Finset.mem_univ _⟩
  exact ⟨a, fun b ↦ ha b (Finset.mem_univ b)⟩

/-- If every pair has nonpositive surplus, leaving everybody single maximizes surplus. -/
lemma empty_isSurplusMaximizer_of_nonpos (v : M → W → ℝ) (hv : ∀ m w, v m w ≤ 0) :
    empty.IsSurplusMaximizer v := by
  intro b
  simpa [totalSurplus, empty] using Finset.sum_nonpos (fun p (_ : p ∈ b.val) ↦ hv p.1 p.2)

/-- In a one-pair market, a nonnegative-surplus pair maximizes surplus. -/
lemma singleton_isSurplusMaximizer [Subsingleton M] [Subsingleton W]
    (m : M) (w : W) (v : M → W → ℝ) (hv : 0 ≤ v m w) :
    (singleton m w).IsSurplusMaximizer v := by
  classical
  intro b
  rw [totalSurplus_singleton]
  have hsubset : b.val ⊆ {(m, w)} := by
    intro p _
    exact Finset.mem_singleton.mpr (Subsingleton.elim _ _)
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg (f := fun p ↦ v p.1 p.2) hsubset
    (fun p (_ : p ∈ ({(m, w)} : Finset (M × W))) _ ↦ by
      simpa only [Subsingleton.elim p (m, w)] using hv)
  simpa [totalSurplus] using hsum

/-- The corresponding undirected edges in the complete bipartite graph. -/
def graphEdges [DecidableEq M] [DecidableEq W] (a : FiniteAllocation M W) :
    Finset (Sym2 (M ⊕ W)) :=
  a.val.image fun p ↦ s(Sum.inl p.1, Sum.inr p.2)

@[simp]
lemma graphEdges_empty [DecidableEq M] [DecidableEq W] :
    (empty : FiniteAllocation M W).graphEdges = ∅ := by
  simp [graphEdges, empty]

/-- Passing to undirected bipartite edges preserves the number of couples. -/
lemma card_graphEdges [DecidableEq M] [DecidableEq W] (a : FiniteAllocation M W) :
    a.graphEdges.card = a.val.card := by
  classical
  apply Finset.card_image_of_injOn
  intro p _ q _ h
  have hpq : p.1 = q.1 ∧ p.2 = q.2 := by simpa [Sym2.eq_iff] using h
  exact Prod.ext hpq.1 hpq.2

/-- A partial allocation is an edge matching of the complete bipartite graph. -/
lemma isEdgeMatching_graphEdges [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (a : FiniteAllocation M W) :
    (completeBipartiteGraph M W).IsEdgeMatching a.graphEdges := by
  classical
  constructor
  · intro e he
    obtain ⟨⟨m, w⟩, _, rfl⟩ := Finset.mem_image.mp he
    simp
  · intro e he f hf
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hf
    by_cases h : p = q
    · exact Or.inl (by subst q; rfl)
    · right
      intro v hmem
      cases v with
      | inl m =>
        have hh : m = p.1 ∧ m = q.1 := by simpa using hmem
        have hm : p.1 = q.1 := hh.1.symm.trans hh.2
        exact h (a.property.1 hp hq hm)
      | inr w =>
        have hh : w = p.2 ∧ w = q.2 := by simpa using hmem
        have hw : p.2 = q.2 := hh.1.symm.trans hh.2
        exact h (a.property.2 hp hq hw)

variable [Fintype M] [Fintype W]

open scoped Classical in
/-- Population counts by observed type. -/
def typePopulation {X : Type*} (t : M → X) (x : X) : ℕ :=
  (Finset.univ.filter fun m ↦ t m = x).card

open scoped Classical in
/-- Counts of married pairs by both observed types. -/
def pairCount {X Y : Type*} (a : FiniteAllocation M W) (tx : M → X) (ty : W → Y)
    (x : X) (y : Y) : ℕ :=
  (a.val.filter fun p ↦ tx p.1 = x ∧ ty p.2 = y).card

omit [Fintype M] [Fintype W] in
@[simp]
lemma pairCount_empty {X Y : Type*} (tx : M → X) (ty : W → Y) (x : X) (y : Y) :
    empty.pairCount tx ty x y = 0 := by
  simp [pairCount, empty]

omit [Fintype M] [Fintype W] in
open scoped Classical in
@[simp]
lemma pairCount_singleton {X Y : Type*} (tx : M → X) (ty : W → Y)
    (m : M) (w : W) (x : X) (y : Y) :
    (singleton m w).pairCount tx ty x y = if tx m = x ∧ ty w = y then 1 else 0 := by
  classical
  change (Finset.filter (fun p : M × W ↦ tx p.1 = x ∧ ty p.2 = y) {(m, w)}).card = _
  rw [Finset.filter_singleton]
  split_ifs <;> simp

open scoped Classical in
/-- Actual unmatched men of the given observed type. -/
def singleMenCount {X : Type*} (a : FiniteAllocation M W) (tx : M → X) (x : X) : ℕ :=
  ((Finset.univ.filter fun m ↦ tx m = x) \ a.val.image Prod.fst).card

open scoped Classical in
/-- Actual unmatched women of the given observed type. -/
def singleWomenCount {Y : Type*} (a : FiniteAllocation M W) (ty : W → Y) (y : Y) : ℕ :=
  ((Finset.univ.filter fun w ↦ ty w = y) \ a.val.image Prod.snd).card

open scoped Classical in
private lemma card_filter_projection {A B X : Type*} [Fintype B]
    (s : Finset A) (f : A → B) (t : B → X) (x : X) (hf : Set.InjOn f (s : Set A)) :
    (s.filter fun a ↦ t (f a) = x).card =
      ((Finset.univ.filter fun b ↦ t b = x) ∩ s.image f).card := by
  classical
  rw [← Finset.card_image_of_injOn (hf.mono (fun _ hz ↦ (Finset.mem_filter.mp hz).1))]
  congr 1
  ext b
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_inter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ⟨ha, hx⟩, rfl⟩
    exact ⟨hx, a, ha, rfl⟩
  · rintro ⟨hx, a, ha, rfl⟩
    exact ⟨a, ⟨ha, hx⟩, rfl⟩

omit [Fintype W] in
/-- The married and single men of every observed type exhaust its population. -/
lemma sum_pairCount_add_singleMenCount {X Y : Type*} [Fintype Y]
    (a : FiniteAllocation M W) (tx : M → X) (ty : W → Y) (x : X) :
    (∑ y, a.pairCount tx ty x y) + a.singleMenCount tx x = typePopulation tx x := by
  classical
  have hfiber : (∑ y, a.pairCount tx ty x y) =
      (a.val.filter fun p ↦ tx p.1 = x).card := by
    simpa [pairCount, Finset.filter_filter, and_assoc] using
      Finset.sum_card_fiberwise_eq_card_filter
        (a.val.filter fun p ↦ tx p.1 = x) Finset.univ (fun p ↦ ty p.2)
  rw [hfiber, card_filter_projection a.val Prod.fst tx x a.property.1]
  exact Finset.card_inter_add_card_sdiff _ _

omit [Fintype M] in
/-- The married and single women of every observed type exhaust its population. -/
lemma sum_pairCount_add_singleWomenCount {X Y : Type*} [Fintype X]
    (a : FiniteAllocation M W) (tx : M → X) (ty : W → Y) (y : Y) :
    (∑ x, a.pairCount tx ty x y) + a.singleWomenCount ty y = typePopulation ty y := by
  classical
  have hfiber : (∑ x, a.pairCount tx ty x y) =
      (a.val.filter fun p ↦ ty p.2 = y).card := by
    simpa [pairCount, Finset.filter_filter, and_comm, and_left_comm, and_assoc] using
      Finset.sum_card_fiberwise_eq_card_filter
        (a.val.filter fun p ↦ ty p.2 = y) Finset.univ (fun p ↦ tx p.1)
  rw [hfiber, card_filter_projection a.val Prod.snd ty y a.property.2]
  exact Finset.card_inter_add_card_sdiff _ _

/-- Aggregate pairs and singles into nonnegative type masses. -/
def marriageTable {X Y : Type*} (a : FiniteAllocation M W) (tx : M → X) (ty : W → Y) :
    MarriageTable X Y where
  marriages x y := a.pairCount tx ty x y
  singleMen x := a.singleMenCount tx x
  singleWomen y := a.singleWomenCount ty y

@[simp]
lemma marriageTable_empty {X Y : Type*} (tx : M → X) (ty : W → Y) :
    empty.marriageTable tx ty = MarriageTable.allSingles
      (fun x ↦ typePopulation tx x) (fun y ↦ typePopulation ty y) := by
  ext <;> simp [marriageTable, pairCount, singleMenCount, singleWomenCount, empty,
    MarriageTable.allSingles, typePopulation]

/-- Aggregation preserves each side's actual population, including unequal totals. -/
lemma marriageTable_hasMargins {X Y : Type*} [Fintype X] [Fintype Y]
    (a : FiniteAllocation M W) (tx : M → X) (ty : W → Y) :
    (a.marriageTable tx ty).HasMargins
      (fun x ↦ typePopulation tx x) (fun y ↦ typePopulation ty y) := by
  constructor
  · intro x
    change (∑ y, (a.pairCount tx ty x y : ℝ≥0)) + a.singleMenCount tx x = typePopulation tx x
    exact_mod_cast a.sum_pairCount_add_singleMenCount tx ty x
  · intro y
    change (∑ x, (a.pairCount tx ty x y : ℝ≥0)) + a.singleWomenCount ty y = typePopulation ty y
    exact_mod_cast a.sum_pairCount_add_singleWomenCount tx ty y

end

end FiniteAllocation

end TransferableUtilityMatching
