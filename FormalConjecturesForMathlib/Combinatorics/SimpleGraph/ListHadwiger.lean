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

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Lattice.Nat

/-!
# List colouring and clique minors

Definitions used in the linear list Hadwiger conjecture. List assignments allow
arbitrary colour types and lists of at least the specified size. Clique minors
are represented by disjoint connected branch sets.

Definitions and short proofs adapted from OpenAI's
[Model.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ListHadwiger/Model.lean)
and [Basic.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ListHadwiger/Basic.lean),
licensed under Apache-2.0. Names, namespace, imports, and notation were changed.
-/

@[expose] public section

namespace SimpleGraph

/-- Lists admit a proper colouring that chooses a colour from each vertex's list. -/
def ListColorable {V : Type} (G : SimpleGraph V) {Color : Type}
    (L : V → Finset Color) : Prop :=
  ∃ c : V → Color, (∀ v, c v ∈ L v) ∧ ∀ ⦃v w⦄, G.Adj v w → c v ≠ c w

/-- Every assignment of at least $k$ colours per vertex admits a list colouring. -/
def Choosable {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (Color : Type) (L : V → Finset Color), (∀ v, k ≤ (L v).card) → G.ListColorable L

/-- The infimum of the list sizes that guarantee a list colouring.
For finite graphs this is the list chromatic number. -/
noncomputable def listChromaticNumber {V : Type} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | G.Choosable k}

/-- A clique minor represented by disjoint connected branch sets. -/
def HasCliqueMinor {V : Type} (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ B : Fin t → Set V,
    (∀ i, (G.induce (B i)).Connected) ∧
    (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
    (∀ i j, i ≠ j → ∃ v ∈ B i, ∃ w ∈ B j, G.Adj v w)

/-- The supremum of the orders of clique minors.
For finite graphs this is the maximum order of a clique minor. -/
noncomputable def hadwigerNumber {V : Type} (G : SimpleGraph V) : ℕ :=
  sSup {t : ℕ | G.HasCliqueMinor t}

theorem hasCliqueMinor_zero {V : Type} (G : SimpleGraph V) : G.HasCliqueMinor 0 := by
  refine ⟨Fin.elim0, ?_, ?_, ?_⟩ <;> intro i <;> exact Fin.elim0 i

theorem not_listColorable_empty {V Color : Type} [Nonempty V] (G : SimpleGraph V) :
    ¬ G.ListColorable (fun _ => (∅ : Finset Color)) := by
  rintro ⟨c, hc, _⟩
  exact Finset.notMem_empty (c (Classical.arbitrary V)) (hc _)

theorem choosable_card {V : Type} [Fintype V] (G : SimpleGraph V) :
    G.Choosable (Fintype.card V) := by
  classical
  intro Color L hL
  have hall : ∀ s : Finset V, s.card ≤ (s.biUnion L).card := by
    intro s
    obtain rfl | hs := s.eq_empty_or_nonempty
    · simp
    obtain ⟨v, hv⟩ := hs
    exact (Finset.card_le_univ s).trans ((hL v).trans
      (Finset.card_le_card (Finset.subset_biUnion_of_mem L hv)))
  obtain ⟨c, hc, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective L).mp hall
  exact ⟨c, hmem, fun _ _ hvw heq => hvw.ne (hc heq)⟩

theorem choosable_listChromaticNumber {V : Type} [Fintype V] (G : SimpleGraph V) :
    G.Choosable G.listChromaticNumber := by
  exact Nat.sInf_mem (s := {k : ℕ | G.Choosable k})
    ⟨Fintype.card V, choosable_card G⟩

theorem HasCliqueMinor.order_le_card {V : Type} [Fintype V] {G : SimpleGraph V}
    {t : ℕ} (h : G.HasCliqueMinor t) : t ≤ Fintype.card V := by
  classical
  obtain ⟨B, hc, hd, _⟩ := h
  have hb : ∀ i, ∃ v, v ∈ B i := fun i => by
    obtain ⟨v⟩ := (hc i).nonempty
    exact ⟨v.val, v.property⟩
  choose v hv using hb
  have hi : Function.Injective v := by
    intro i j hij
    by_contra hn
    exact Set.disjoint_left.mp (hd i j hn) (hv i) (by
      rw [hij]
      exact hv j)
  simpa using Fintype.card_le_of_injective v hi

theorem hasCliqueMinor_hadwigerNumber {V : Type} [Fintype V] (G : SimpleGraph V) :
    G.HasCliqueMinor G.hadwigerNumber := by
  exact Nat.sSup_mem (s := {t : ℕ | G.HasCliqueMinor t}) ⟨0, hasCliqueMinor_zero G⟩
    ⟨Fintype.card V, fun _ h => h.order_le_card⟩

end SimpleGraph
