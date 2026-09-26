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
- [EOZ93] Erdős, P., Ordman, E. T. and Zalcstein, Y., Clique partitions of chordal graphs.
  Combin. Probab. Comput. (1993), 409-415.
- [CEO94] Chen, G., Erdős, P. and Ordman, E. T., Clique partitions of split graphs.
  Combinatorics, graph theory, algorithms and applications (Beijing, 1993) (1994).
-/

@[expose] public section

open Filter SimpleGraph

namespace Erdos81

variable {V : Type*}

/-- A graph is *chordal* if it has no induced cycle of length at least $4$. -/
def IsChordal (G : SimpleGraph V) : Prop :=
  ∀ k, 4 ≤ k → ¬ (cycleGraph k).IsIndContained G

/-- A graph is a *split graph* if its vertices split into a clique and an independent set. -/
def IsSplit (G : SimpleGraph V) : Prop :=
  ∃ S : Set V, G.IsClique S ∧ G.IsIndepSet Sᶜ

/-- `P` partitions the edges of `G` into cliques: each member of `P` is a clique of `G` with at
least two vertices, and each edge of `G` lies in exactly one member of `P`. -/
def IsCliqueEdgePartition (G : SimpleGraph V) (P : Finset (Finset V)) : Prop :=
  (∀ s ∈ P, 2 ≤ s.card ∧ G.IsClique (s : Set V)) ∧
    ∀ u v, G.Adj u v → ∃! s, s ∈ P ∧ u ∈ s ∧ v ∈ s

/--
Let $G$ be a chordal graph on $n$ vertices, that is, $G$ has no induced cycle of length
greater than $3$. Can the edges of $G$ be partitioned into $n^2/6+O(n)$ many cliques?
-/
@[category research open, AMS 5]
theorem erdos_81 :
    answer(sorry) ↔ ∃ C : ℝ, ∀ n, ∀ G : SimpleGraph (Fin n), IsChordal G →
      ∃ P, IsCliqueEdgePartition G P ∧ (P.card : ℝ) ≤ (n : ℝ) ^ 2 / 6 + C * n := by
  sorry

/--
The bound $n^2/6$ in `erdos_81` cannot be lowered: some split graphs, which are chordal, need
$n^2/6-O(n)$ cliques [EOZ93].
-/
@[category research solved, AMS 5]
theorem erdos_81.variants.lower_bound :
    ∃ C : ℝ, ∀ n, ∃ G : SimpleGraph (Fin n), IsSplit G ∧
      ∀ P, IsCliqueEdgePartition G P → (n : ℝ) ^ 2 / 6 - C * n ≤ P.card := by
  sorry

/--
Erdős, Ordman and Zalcstein [EOZ93]: there is $c>0$ such that the edges of every chordal
graph on $n$ vertices can be partitioned into $(1-c)n^2/4$ cliques.

The bound is stated for large $n$. For $n=2$ the single edge needs one clique, which is more
than $(1-c)n^2/4$.
-/
@[category research solved, AMS 5]
theorem erdos_81.variants.eoz :
    ∃ c > (0 : ℝ), ∀ᶠ n in atTop, ∀ G : SimpleGraph (Fin n), IsChordal G →
      ∃ P, IsCliqueEdgePartition G P ∧ (P.card : ℝ) ≤ (1 - c) * (n : ℝ) ^ 2 / 4 := by
  sorry

/--
Chen, Erdős and Ordman [CEO94]: the edges of every split graph on $n$ vertices can be
partitioned into $\frac{3}{16}n^2+O(n)$ cliques.
-/
@[category research solved, AMS 5]
theorem erdos_81.variants.split :
    ∃ C : ℝ, ∀ n, ∀ G : SimpleGraph (Fin n), IsSplit G →
      ∃ P, IsCliqueEdgePartition G P ∧ (P.card : ℝ) ≤ 3 * (n : ℝ) ^ 2 / 16 + C * n := by
  sorry

/-- The cycle $C_4$ is not chordal. -/
@[category test, AMS 5]
theorem not_isChordal_cycleGraph_four : ¬ IsChordal (cycleGraph 4) :=
  fun h ↦ h 4 le_rfl ⟨Embedding.refl⟩

/-- The edges of `G`, each seen as a clique, form a clique edge partition. So the partitions in
`erdos_81` always exist. -/
@[category test, AMS 5]
theorem exists_isCliqueEdgePartition [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    ∃ P, IsCliqueEdgePartition G P ∧ P.card = G.edgeFinset.card := by
  refine ⟨G.edgeFinset.image Sym2.toFinset, ⟨?_, ?_⟩, ?_⟩
  · simp only [Finset.mem_image, mem_edgeFinset]
    rintro s ⟨e, he, rfl⟩
    induction e using Sym2.ind with
    | h a b =>
      rw [mem_edgeSet] at he
      rw [Sym2.toFinset_mk_eq, Finset.card_pair he.ne, Finset.coe_pair]
      exact ⟨le_rfl, isClique_pair.mpr fun _ ↦ he⟩
  · intro u v huv
    refine ⟨s(u, v).toFinset,
      ⟨Finset.mem_image.mpr ⟨s(u, v), by simpa using huv, rfl⟩, by simp, by simp⟩, ?_⟩
    rintro s ⟨hs, hu, hv⟩
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hs
    rw [Sym2.mem_toFinset] at hu hv
    rw [(Sym2.mem_and_mem_iff huv.ne).mp ⟨hu, hv⟩]
  · refine Finset.card_image_of_injOn fun e he e' _ h ↦ ?_
    simp only [mem_edgeFinset, Finset.mem_coe] at he
    induction e using Sym2.ind with
    | h a b =>
      have ha : a ∈ e'.toFinset := by rw [← h]; simp
      have hb : b ∈ e'.toFinset := by rw [← h]; simp
      rw [Sym2.mem_toFinset] at ha hb
      exact ((Sym2.mem_and_mem_iff ((mem_edgeSet G).mp he).ne).mp ⟨ha, hb⟩).symm

/-- Every split graph is chordal, so `erdos_81.variants.split` is a special case of
`erdos_81`. -/
@[category textbook, AMS 5]
theorem IsSplit.isChordal {G : SimpleGraph V} (hG : IsSplit G) : IsChordal G := by
  obtain ⟨S, hS, hI⟩ := hG
  rintro k hk ⟨f⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  have adj (a : Fin (m + 4)) : (cycleGraph (m + 4)).Adj a (a + 1) :=
    cycleGraph_adj.mpr (Or.inr (by simp))
  have two : (1 + 1 : Fin (m + 4)) ≠ 0 ∧ (1 + 1 : Fin (m + 4)) ≠ 1 ∧
      (-(1 + 1) : Fin (m + 4)) ≠ 1 := by
    refine ⟨?_, ?_, ?_⟩ <;> intro h <;> rw [Fin.ext_iff] at h
    · simp [Fin.val_add, Nat.mod_eq_of_lt] at h
    · simp [Fin.val_add, Nat.mod_eq_of_lt] at h
    · rw [Fin.val_neg'] at h
      simp [Fin.val_add, Nat.mod_eq_of_lt] at h
  have noK (a : Fin (m + 4)) (ha : f a ∈ S) (hb : f (a + 1 + 1) ∈ S) : False := by
    have hne : a ≠ a + 1 + 1 := fun h ↦ two.1 (by rw [add_assoc] at h; simpa using h.symm)
    refine (f.map_adj_iff.mp (hS ha hb (f.injective.ne hne))).elim ?_ ?_
    · exact fun h ↦ two.2.2 (by rwa [show -(1 + 1) = a - (a + 1 + 1) by abel])
    · exact fun h ↦ two.2.1 (by rwa [show 1 + 1 = a + 1 + 1 - a by abel])
  have noI (a : Fin (m + 4)) (ha : f a ∉ S) (hb : f (a + 1) ∉ S) : False :=
    hI ha hb (f.map_adj_iff.mpr (adj a)).ne (f.map_adj_iff.mpr (adj a))
  by_cases h1 : f (0 + 1) ∈ S
  · have h3 : f (0 + 1 + 1 + 1) ∉ S := noK _ h1
    have h2 : f (0 + 1 + 1) ∈ S := by_contra fun h ↦ noI _ h h3
    have h4 : f (0 + 1 + 1 + 1 + 1) ∈ S := by_contra (noI _ h3)
    exact noK _ h2 h4
  · have h0 : f 0 ∈ S := by_contra fun h ↦ noI _ h h1
    have h2 : f (0 + 1 + 1) ∈ S := by_contra (noI _ h1)
    exact noK _ h0 h2

end Erdos81
