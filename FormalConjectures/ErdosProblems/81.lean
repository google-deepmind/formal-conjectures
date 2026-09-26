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

public import FormalConjecturesUtil

/-!
# Erdős Problem 81

*References:*
- [erdosproblems.com/81](https://www.erdosproblems.com/81)
- [EOZ93] Erdős, Paul and Ordman, Edward T. and Zalcstein, Yechezkel, *Clique partitions of
  chordal graphs*. Combin. Probab. Comput. (1993), 409-415.
- [CEO94] Chen, Guantao and Erdős, Paul and Ordman, Edward T., *Clique partitions of split
  graphs*. Combinatorics, graph theory, algorithms and applications (Beijing, 1993) (1994),
  21-30.
-/

@[expose] public section

open Filter

namespace SimpleGraph

variable {V : Type*}

/-- A graph is *chordal* if it contains no induced cycle of length `k ≥ 4`. -/
def IsChordal (G : SimpleGraph V) : Prop :=
  ∀ k : ℕ, 4 ≤ k → ¬ (cycleGraph k).IsIndContained G

/-- `P` is a partition of the edges of `G` into cliques: each member of `P` is a clique
of `G` with at least two vertices, and every edge of `G` lies in exactly one member of `P`. -/
def IsCliqueEdgePartition (G : SimpleGraph V) (P : Finset (Finset V)) : Prop :=
  (∀ s ∈ P, 2 ≤ s.card ∧ G.IsClique (s : Set V)) ∧
  ∀ u v : V, G.Adj u v → ∃! s, s ∈ P ∧ u ∈ s ∧ v ∈ s

/-- A graph is a *split graph* if its vertex set splits into a clique and an
independent set. -/
def IsSplitGraph (G : SimpleGraph V) : Prop :=
  ∃ S : Set V, G.IsClique S ∧ G.IsIndepSet Sᶜ

end SimpleGraph

namespace Erdos81

open SimpleGraph

/--
Let $G$ be a chordal graph on $n$ vertices, that is, $G$ has no induced cycle of length
greater than $3$. Can the edges of $G$ be partitioned into $n^2/6 + O(n)$ many cliques?

This would be best possible: consider all edges between a complete graph on $n/3$ vertices
and an empty graph on $2n/3$ vertices.
-/
@[category research open, AMS 5]
theorem erdos_81 :
    answer(sorry) ↔
      ∃ C : ℝ, ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), G.IsChordal →
        ∃ P : Finset (Finset (Fin n)), G.IsCliqueEdgePartition P ∧
          (P.card : ℝ) ≤ (n : ℝ) ^ 2 / 6 + C * n := by
  sorry

/--
Erdős, Ordman, and Zalcstein [EOZ93] proved that the edges of every chordal graph on $n$
vertices can be partitioned into $(1/4 - \varepsilon) n^2$ many cliques, for some small
constant $\varepsilon > 0$.
-/
@[category research solved, AMS 5]
theorem erdos_81.variants.eoz :
    ∃ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n), G.IsChordal →
      ∃ P : Finset (Finset (Fin n)), G.IsCliqueEdgePartition P ∧
        (P.card : ℝ) ≤ (1 / 4 - ε) * (n : ℝ) ^ 2 := by
  sorry

/--
Chen, Erdős, and Ordman [CEO94] proved that the edges of every split graph on $n$ vertices
(a graph whose vertices split into a clique and an independent set) can be partitioned into
$\frac{3}{16} n^2 + O(n)$ many cliques.
-/
@[category research solved, AMS 5]
theorem erdos_81.variants.split :
    ∃ C : ℝ, ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), G.IsSplitGraph →
      ∃ P : Finset (Finset (Fin n)), G.IsCliqueEdgePartition P ∧
        (P.card : ℝ) ≤ 3 * (n : ℝ) ^ 2 / 16 + C * n := by
  sorry

/-- Every finite graph has a clique edge partition with one clique per edge. -/
@[category API, AMS 5]
theorem exists_cliqueEdgePartition_card_eq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ P : Finset (Finset V), G.IsCliqueEdgePartition P ∧ P.card = G.edgeFinset.card := by
  refine ⟨G.edgeFinset.image Sym2.toFinset, ⟨?_, ?_⟩, ?_⟩
  · simp only [Finset.mem_image, mem_edgeFinset]
    rintro s ⟨e, he, rfl⟩
    induction e using Sym2.ind with
    | h a b =>
      rw [mem_edgeSet] at he
      rw [Sym2.toFinset_mk_eq, Finset.card_pair he.ne, Finset.coe_pair]
      exact ⟨le_rfl, isClique_pair.mpr (fun _ => he)⟩
  · intro u v huv
    refine ⟨s(u, v).toFinset,
      ⟨Finset.mem_image.mpr ⟨s(u, v), by simpa using huv, rfl⟩, by simp, by simp⟩, ?_⟩
    rintro s ⟨hs, hu, hv⟩
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hs
    rw [Sym2.mem_toFinset] at hu hv
    rw [(Sym2.mem_and_mem_iff huv.ne).mp ⟨hu, hv⟩]
  · apply Finset.card_image_of_injOn
    intro e he e' _ h
    simp only [mem_edgeFinset, Finset.mem_coe] at he
    induction e using Sym2.ind with
    | h a b =>
      have hab := (mem_edgeSet G).mp he
      have ha : a ∈ e'.toFinset := by rw [← h]; simp
      have hb : b ∈ e'.toFinset := by rw [← h]; simp
      rw [Sym2.mem_toFinset] at ha hb
      exact ((Sym2.mem_and_mem_iff hab.ne).mp ⟨ha, hb⟩).symm

@[category API, AMS 5]
lemma cycleGraph_adj_succ (m : ℕ) (a : Fin (m + 4)) : (cycleGraph (m + 4)).Adj a (a + 1) :=
  (cycleGraph_adj (n := m + 2)).mpr (Or.inr (by simp))

@[category API, AMS 5]
lemma cycleGraph_not_adj_add_two (m : ℕ) (a : Fin (m + 4)) :
    a ≠ a + 1 + 1 ∧ ¬ (cycleGraph (m + 4)).Adj a (a + 1 + 1) := by
  have key : (1 + 1 : Fin (m + 4)) ≠ 1 ∧ (1 + 1 : Fin (m + 4)) ≠ 0 ∧
      (-(1 + 1) : Fin (m + 4)) ≠ 1 := by
    refine ⟨?_, ?_, ?_⟩ <;> intro h <;> rw [Fin.ext_iff] at h
    · simp [Fin.val_add, Nat.mod_eq_of_lt] at h
    · simp [Fin.val_add, Nat.mod_eq_of_lt] at h
    · rw [Fin.val_neg'] at h
      simp [Fin.val_add, Nat.mod_eq_of_lt] at h
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := congrArg (fun x => x - a) h
    simp only [sub_self] at this
    exact key.2.1 (by rw [this]; abel)
  · rcases (cycleGraph_adj (n := m + 2)).mp h with h | h
    · exact key.2.2 (by rw [show -(1 + 1 : Fin (m + 4)) = a - (a + 1 + 1) by abel]; exact h)
    · exact key.1 (by rw [show (1 + 1 : Fin (m + 4)) = a + 1 + 1 - a by abel]; exact h)

/-- Every split graph is chordal. -/
@[category API, AMS 5]
theorem IsSplitGraph.isChordal {V : Type*} {G : SimpleGraph V} (hG : G.IsSplitGraph) :
    G.IsChordal := by
  obtain ⟨S, hS, hI⟩ := hG
  intro k hk ⟨f⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  have noK : ∀ a, f a ∈ S → f (a + 1 + 1) ∈ S → False := fun a ha hb => by
    obtain ⟨hne, hna⟩ := cycleGraph_not_adj_add_two m a
    exact hna (f.map_adj_iff.mp (hS ha hb (f.injective.ne hne)))
  have noI : ∀ a, f a ∉ S → f (a + 1) ∉ S → False := fun a ha hb => by
    have h := f.map_adj_iff.mpr (cycleGraph_adj_succ m a)
    exact hI ha hb h.ne h
  by_cases h1 : f (0 + 1) ∈ S
  · have h3 : f (0 + 1 + 1 + 1) ∉ S := fun h => noK _ h1 h
    have h2 : f (0 + 1 + 1) ∈ S := by_contra fun h => noI _ h h3
    have h4 : f (0 + 1 + 1 + 1 + 1) ∈ S := by_contra fun h => noI _ h3 h
    exact noK _ h2 h4
  · have h0 : f 0 ∈ S := by_contra fun h => noI _ h h1
    have h2 : f (0 + 1 + 1) ∈ S := by_contra fun h => noI _ h1 h
    exact noK _ h0 h2

end Erdos81
