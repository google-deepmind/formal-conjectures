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

import FormalConjecturesUtil

/-!
# Size, Order, and Connected Domination

*References:*
- [S. Mukwembi, _Size, order, and connected domination_,
  Canad. Math. Bull. 57 (2014), no. 1, 141–144](https://doi.org/10.4153/CMB-2013-020-5)
-/

namespace SizeOrderConnectedDomination

open SimpleGraph

/-- `Q3`: the 3-dimensional hypercube on `Fin 8`; two vertices are adjacent when
their indices differ in exactly one bit. Used below as the counterexample to
Theorem 2.1 of the paper. -/
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
  · let S : Set ℕ :=
      {n | ∃ D : Finset (Fin 8), Q3.IsConnectedDominating (D : Set (Fin 8)) ∧ D.card = n}
    have hS : S.Nonempty :=
      ⟨4, ({0, 1, 2, 3} : Finset (Fin 8)), Q3_connectedDominating_four, rfl⟩
    obtain ⟨D, hD, hDcard⟩ := Nat.sInf_mem hS
    rw [show Q3.connectedDominationNumber = sInf S by rfl, ← hDcard]
    exact Q3_cds_card_ge_four D hD

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem Q3_card_edges : Q3.edgeFinset.card = 12 := by decide

/--
**Theorem 2.1** of [S. Mukwembi, _Size, order, and connected domination_,
Canad. Math. Bull. 57 (2014), no. 1, 141–144](https://doi.org/10.4153/CMB-2013-020-5)
claims: if $G$ is a connected triangle-free graph of order $n$ and size $m$ with
connected domination number $\gamma_c$, then
$$m \le \frac{(n - \gamma_c)^2}{4} + n - 1.$$

The claim is **false**: the 3-dimensional hypercube $Q_3$ is a counterexample,
with $n = 8$, $m = 12$ and $\gamma_c = 4$, so the asserted bound reads
$12 \le (8-4)^2/4 + 8 - 1 = 11$. The gap in the paper's proof (p. 143) is the
unjustified assertion that there is an edge $uv$ with
$\gamma_c(G) \le \gamma_c(G - \{u, v\})$: in $Q_3$, removing any adjacent pair
of vertices leaves a graph with connected domination number $2 < 4$.

The corollaries of the paper (Corollary 2.2 and 2.3, on leaf numbers of
triangle-free graphs) remain true; Corollary 2.2 is Graffiti.pc Conjecture 1.1,
recorded as `WrittenOnTheWallII.GraphConjecture2.conjecture2`.
-/
@[category research solved, AMS 5]
theorem mukwembi_theorem_2_1 : answer(False) ↔
    ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) [DecidableRel G.Adj],
      G.Connected → G.CliqueFree 3 →
      (G.edgeFinset.card : ℝ) ≤
        ((Fintype.card α : ℝ) - (G.connectedDominationNumber : ℝ)) ^ 2 / 4
          + (Fintype.card α : ℝ) - 1 := by
  refine iff_of_false (fun hf => hf.elim) fun h => ?_
  have hQ3 := h (Fin 8) Q3 Q3_connected Q3_cliqueFree
  rw [Q3_card_edges, Q3_connectedDominationNumber] at hQ3
  norm_num [Fintype.card_fin] at hQ3

end SizeOrderConnectedDomination
