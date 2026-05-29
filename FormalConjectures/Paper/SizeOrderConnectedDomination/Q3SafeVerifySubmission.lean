/-
Copyright 2025 The Formal Conjectures Authors.

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

import FormalConjectures.Util.ProblemImports
import FormalConjectures.WrittenOnTheWallII.GraphConjecture2

/-! SafeVerify submission: disproof of Mukwembi's Theorem 2.1 via Q₃.
Self-contained (no native_decide) so SafeVerify can replay it. -/

open SimpleGraph

/-- Q₃: the 3-dimensional hypercube on Fin 8. -/
private def Q3 : SimpleGraph (Fin 8) where
  Adj u v := u ≠ v ∧ (u.val ^^^ v.val = 1 ∨ u.val ^^^ v.val = 2 ∨ u.val ^^^ v.val = 4)
  symm u v := by intro ⟨h1, h2⟩; exact ⟨h1.symm, by simp [Nat.xor_comm] at h2 ⊢; exact h2⟩
  loopless v := by intro ⟨h, _⟩; exact h rfl

private instance : DecidableRel Q3.Adj := fun u v =>
  show Decidable (u ≠ v ∧ _) from inferInstance

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem Q3_connected : Q3.Connected := by
  constructor; intro a b
  fin_cases a <;> fin_cases b <;> first | exact Reachable.refl _ | decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem Q3_cliqueFree : Q3.CliqueFree 3 := by
  intro s hs; simp only [isNClique_iff, isClique_iff] at hs; revert hs; revert s; decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem Q3_connectedDominating_four :
    Q3.IsConnectedDominating (↑({0, 1, 2, 3} : Finset (Fin 8)) : Set (Fin 8)) := by
  constructor
  · intro v; fin_cases v <;> simp [Q3]
  · refine Connected.mk ?_; intro a b
    fin_cases a <;> fin_cases b <;> first | exact Reachable.refl _ | decide

-- Expanded form for decide to work on
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem Q3_not_cds_singleton_expanded (a : Fin 8) :
    ¬ (((∀ v : Fin 8, v ∈ (↑({a} : Finset (Fin 8)) : Set (Fin 8)) ∨
        ∃ w ∈ (↑({a} : Finset (Fin 8)) : Set (Fin 8)), Q3.Adj v w)) ∧
       (induce (↑({a} : Finset (Fin 8)) : Set (Fin 8)) Q3).Connected) := by
  fin_cases a <;> decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem Q3_not_cds_pair_expanded (a b : Fin 8) :
    ¬ (((∀ v : Fin 8, v ∈ (↑({a, b} : Finset (Fin 8)) : Set (Fin 8)) ∨
        ∃ w ∈ (↑({a, b} : Finset (Fin 8)) : Set (Fin 8)), Q3.Adj v w)) ∧
       (induce (↑({a, b} : Finset (Fin 8)) : Set (Fin 8)) Q3).Connected) := by
  fin_cases a <;> fin_cases b <;> decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 16000000 in
private theorem Q3_not_cds_triple_expanded (a b c : Fin 8) :
    ¬ (((∀ v : Fin 8, v ∈ (↑({a, b, c} : Finset (Fin 8)) : Set (Fin 8)) ∨
        ∃ w ∈ (↑({a, b, c} : Finset (Fin 8)) : Set (Fin 8)), Q3.Adj v w)) ∧
       (induce (↑({a, b, c} : Finset (Fin 8)) : Set (Fin 8)) Q3).Connected) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide

private theorem Q3_not_cds_singleton (a : Fin 8) :
    ¬ Q3.IsConnectedDominating (↑({a} : Finset (Fin 8)) : Set (Fin 8)) := by
  intro h
  exact Q3_not_cds_singleton_expanded a <|
    by simpa [IsConnectedDominating, IsDominating] using h

private theorem Q3_not_cds_pair (a b : Fin 8) :
    ¬ Q3.IsConnectedDominating (↑({a, b} : Finset (Fin 8)) : Set (Fin 8)) := by
  intro h
  exact Q3_not_cds_pair_expanded a b <|
    by simpa [IsConnectedDominating, IsDominating] using h

private theorem Q3_not_cds_triple (a b c : Fin 8) :
    ¬ Q3.IsConnectedDominating (↑({a, b, c} : Finset (Fin 8)) : Set (Fin 8)) := by
  intro h
  exact Q3_not_cds_triple_expanded a b c <|
    by simpa [IsConnectedDominating, IsDominating] using h

private theorem Q3_cds_card_ge_four
    (D : Finset (Fin 8)) (hD : Q3.IsConnectedDominating (D : Set (Fin 8))) :
    4 ≤ D.card := by
  by_contra hlt
  have hne : D.Nonempty := by
    by_contra he; rw [Finset.not_nonempty_iff_eq_empty] at he; subst he
    have := hD.1 0; simp at this
  have : D.card = 1 ∨ D.card = 2 ∨ D.card = 3 := by
    have := Finset.one_le_card.mpr hne; omega
  rcases this with h1 | h2 | h3
  · rcases Finset.card_eq_one.mp h1 with ⟨a, rfl⟩
    exact Q3_not_cds_singleton a hD
  · rcases Finset.card_eq_two.mp h2 with ⟨a, b, _, rfl⟩
    exact Q3_not_cds_pair a b hD
  · rcases Finset.card_eq_three.mp h3 with ⟨a, b, c, _, _, _, rfl⟩
    exact Q3_not_cds_triple a b c hD

private theorem Q3_connectedDominationNumber : Q3.connectedDominationNumber = 4 := by
  apply le_antisymm
  · apply Nat.sInf_le
    exact ⟨({0, 1, 2, 3} : Finset (Fin 8)), Q3_connectedDominating_four, rfl⟩
  · let S : Set ℕ := {n | ∃ D : Finset (Fin 8), Q3.IsConnectedDominating (D : Set (Fin 8)) ∧ D.card = n}
    have hS : S.Nonempty :=
      ⟨4, ({0, 1, 2, 3} : Finset (Fin 8)), Q3_connectedDominating_four, rfl⟩
    obtain ⟨D, hD, hDcard⟩ := Nat.sInf_mem hS
    rw [show Q3.connectedDominationNumber = sInf S by rfl, ← hDcard]
    exact Q3_cds_card_ge_four D hD

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem Q3_card_edges : Q3.edgeFinset.card = 12 := by decide

private theorem Q3_violates_bound :
    (Q3.edgeFinset.card : ℝ) >
      ((Fintype.card (Fin 8) : ℝ) - (Q3.connectedDominationNumber : ℝ)) ^ 2 / 4
        + (Fintype.card (Fin 8) : ℝ) - 1 := by
  simp only [Q3_card_edges, Q3_connectedDominationNumber, Fintype.card_fin]
  norm_num

theorem mukwembi_size_bound.disproof :
    ∃ (α : Type) (_ : Fintype α) (_ : DecidableEq α) (_ : Nonempty α) (_ : Nontrivial α)
      (G : SimpleGraph α) (_ : DecidableRel G.Adj) (_ : G.Connected) (_ : G.CliqueFree 3),
      ¬ ((G.edgeFinset.card : ℝ) ≤
        ((Fintype.card α : ℝ) - (G.connectedDominationNumber : ℝ)) ^ 2 / 4
        + (Fintype.card α : ℝ) - 1) := by
  refine ⟨Fin 8, inferInstance, inferInstance, inferInstance, inferInstance,
          Q3, inferInstance, Q3_connected, Q3_cliqueFree, ?_⟩
  push_neg
  exact Q3_violates_bound
