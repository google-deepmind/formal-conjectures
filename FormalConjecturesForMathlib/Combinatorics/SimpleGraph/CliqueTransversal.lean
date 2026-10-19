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

public import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Clique transversals

A clique transversal meets every maximal clique with at least two vertices.
In particular, isolated vertices need not belong to a clique transversal.

*Reference:* Erdős, P., Gallai, T., and Tuza, Z., *Covering the cliques of a graph with
vertices*. Discrete Math. (1992), 279-289.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A set meeting every nontrivial maximal clique of a graph. -/
def IsCliqueTransversal (G : SimpleGraph V) (s : Set V) : Prop :=
  ∀ t : Set V, Maximal G.IsClique t → t.Nontrivial → (s ∩ t).Nonempty

lemma isCliqueTransversal_univ (G : SimpleGraph V) : G.IsCliqueTransversal Set.univ := by
  intro t _ ht
  simpa using ht.nonempty

lemma isCliqueTransversal_bot (s : Set V) : (⊥ : SimpleGraph V).IsCliqueTransversal s := by
  intro t ht hnt
  exact (hnt.not_subsingleton ht.1.subsingleton).elim

/-- The least size of a clique transversal, ignoring isolated vertices. -/
noncomputable def cliqueTransversalNum (G : SimpleGraph V) [Fintype V] : ℕ :=
  sInf {k | ∃ s : Finset V, G.IsCliqueTransversal (s : Set V) ∧ s.card = k}

variable [Fintype V]

lemma cliqueTransversalNum_le_card {s : Finset V} (hs : G.IsCliqueTransversal s) :
    G.cliqueTransversalNum ≤ s.card :=
  Nat.sInf_le ⟨s, hs, rfl⟩

lemma exists_cliqueTransversal_card_eq (G : SimpleGraph V) :
    ∃ s : Finset V, G.IsCliqueTransversal (s : Set V) ∧ s.card = G.cliqueTransversalNum := by
  have hne : {k | ∃ s : Finset V, G.IsCliqueTransversal (s : Set V) ∧ s.card = k}.Nonempty :=
    ⟨_, Finset.univ, by simpa using G.isCliqueTransversal_univ, rfl⟩
  exact Nat.sInf_mem hne

lemma cliqueTransversalNum_le_iff {k : ℕ} :
    G.cliqueTransversalNum ≤ k ↔
      ∃ s : Finset V, G.IsCliqueTransversal (s : Set V) ∧ s.card ≤ k := by
  constructor
  · intro h
    obtain ⟨s, hs, hcard⟩ := G.exists_cliqueTransversal_card_eq
    exact ⟨s, hs, hcard.trans_le h⟩
  · rintro ⟨s, hs, hcard⟩
    exact (cliqueTransversalNum_le_card hs).trans hcard

lemma cliqueTransversalNum_le_card_univ (G : SimpleGraph V) :
    G.cliqueTransversalNum ≤ Fintype.card V := by
  simpa using cliqueTransversalNum_le_card
    (s := Finset.univ) (by simpa using G.isCliqueTransversal_univ)

@[simp] lemma cliqueTransversalNum_bot : (⊥ : SimpleGraph V).cliqueTransversalNum = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa using cliqueTransversalNum_le_card (G := (⊥ : SimpleGraph V)) (s := ∅)
    (by simpa using isCliqueTransversal_bot (∅ : Set V))

@[simp] lemma cliqueTransversalNum_of_isEmpty [IsEmpty V] (G : SimpleGraph V) :
    G.cliqueTransversalNum = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa using G.cliqueTransversalNum_le_card_univ

end SimpleGraph
