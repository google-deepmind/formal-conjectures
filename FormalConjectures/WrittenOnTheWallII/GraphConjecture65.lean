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
# Written on the Wall II - Conjecture 65

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Counterexample

The conjecture is false. Start with the path $v_0-v_1-\cdots-v_{12}$ and attach one
triangle at $v_1$ and another at $v_{11}$. The resulting graph has $17$ vertices.
Its only minimum-degree vertices are $v_0$ and $v_{12}$, at distance $12$, while its
only maximum-degree vertices are $v_1$ and $v_{11}$, at distance $10$. Thus the
conjectured lower bound is $12 + \lceil 10/3 \rceil = 16$.

Every induced forest must omit at least one vertex from each of the two vertex-disjoint
triangles, so it has at most $15$ vertices. Conversely, deleting one non-path vertex
from each triangle leaves a tree on $15$ vertices.
-/

namespace WrittenOnTheWallII.GraphConjecture65

open Classical SimpleGraph Finset

namespace Counterexample

/-- The counterexample: a path on vertices $0,\ldots,12$, with triangles attached at
vertices $1$ and $11$. -/
abbrev graph : SimpleGraph (Fin 17) :=
  SimpleGraph.fromEdgeSet {
    s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 5), s(5, 6),
    s(6, 7), s(7, 8), s(8, 9), s(9, 10), s(10, 11), s(11, 12),
    s(1, 13), s(1, 14), s(13, 14),
    s(11, 15), s(11, 16), s(15, 16)
  }

/-- The counterexample is connected. -/
@[category API, AMS 5]
lemma connected : graph.Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨0, ?_⟩
  have step (u v : Fin 17) (h : graph.Reachable 0 u) (huv : graph.Adj u v) :
      graph.Reachable 0 v := h.trans huv.reachable
  have h0 : graph.Reachable 0 0 := by simp
  have h1 := step 0 1 h0 (by decide)
  have h2 := step 1 2 h1 (by decide)
  have h3 := step 2 3 h2 (by decide)
  have h4 := step 3 4 h3 (by decide)
  have h5 := step 4 5 h4 (by decide)
  have h6 := step 5 6 h5 (by decide)
  have h7 := step 6 7 h6 (by decide)
  have h8 := step 7 8 h7 (by decide)
  have h9 := step 8 9 h8 (by decide)
  have h10 := step 9 10 h9 (by decide)
  have h11 := step 10 11 h10 (by decide)
  have h12 := step 11 12 h11 (by decide)
  have h13 := step 1 13 h1 (by decide)
  have h14 := step 1 14 h1 (by decide)
  have h15 := step 11 15 h11 (by decide)
  have h16 := step 11 16 h11 (by decide)
  intro v
  fin_cases v <;> assumption

/-- The minimum-degree vertices of the counterexample are the two path endpoints. -/
@[category API, AMS 5]
lemma min_degree_vertices :
    {v | graph.degree v = graph.minDegree} = ({0, 12} : Set (Fin 17)) := by
  ext v
  fin_cases v <;> decide

/-- The maximum-degree vertices of the counterexample are the two triangle attachment points. -/
@[category API, AMS 5]
lemma max_degree_vertices :
    {v | graph.degree v = graph.maxDegree} = ({1, 11} : Set (Fin 17)) := by
  ext v
  fin_cases v <;> decide

/-- The minimum distance between minimum-degree vertices is $12$. -/
@[category API, AMS 5]
lemma distMin_min_degree_vertices : distMin graph ({0, 12} : Set (Fin 17)) = 12 := by
  rw [show ({0, 12} : Set (Fin 17)) = ↑({0, 12} : Finset (Fin 17)) by simp,
    distMin_eq_computableDistMin]
  decide

/-- The minimum distance between maximum-degree vertices is $10$. -/
@[category API, AMS 5]
lemma distMin_max_degree_vertices : distMin graph ({1, 11} : Set (Fin 17)) = 10 := by
  rw [show ({1, 11} : Set (Fin 17)) = ↑({1, 11} : Finset (Fin 17)) by simp,
    distMin_eq_computableDistMin]
  decide

/-- An acyclic induced subgraph cannot contain all three vertices of a triangle. -/
@[category API, AMS 5]
lemma triangle_not_subset_of_isAcyclic (S : Finset (Fin 17))
    (hS : (graph.induce S).IsAcyclic) {a b c : Fin 17}
    (hab : graph.Adj a b) (hbc : graph.Adj b c) (hca : graph.Adj c a) :
    ¬({a, b, c} : Finset (Fin 17)) ⊆ S := by
  intro hsub
  have ha : a ∈ S := hsub (by simp)
  have hb : b ∈ S := hsub (by simp)
  have hc : c ∈ S := hsub (by simp)
  let va : S := ⟨a, ha⟩
  let vb : S := ⟨b, hb⟩
  let vc : S := ⟨c, hc⟩
  have hab' : (graph.induce S).Adj va vb := hab
  have hbc' : (graph.induce S).Adj vb vc := hbc
  have hca' : (graph.induce S).Adj vc va := hca
  let cycle : (graph.induce S).Walk va va :=
    .cons hab' (.cons hbc' (.cons hca' .nil))
  exact hS cycle (by
    rw [Walk.isCycle_def]
    refine ⟨?_, by simp [cycle], ?_⟩
    · rw [Walk.isTrail_def]
      simp [cycle, va, vb, vc, hab.ne, hab.ne.symm, hbc.ne,
        hca.ne, hca.ne.symm]
    · simp [cycle, va, vb, vc, hab.ne.symm, hbc.ne, hca.ne])

/-- Every induced forest in the counterexample has at most $15$ vertices. -/
@[category API, AMS 5]
lemma forest_card_le_fifteen (S : Finset (Fin 17)) (hS : (graph.induce S).IsAcyclic) :
    S.card ≤ 15 := by
  have hfirst : ¬({1, 13, 14} : Finset (Fin 17)) ⊆ S :=
    triangle_not_subset_of_isAcyclic S hS (by decide) (by decide) (by decide)
  have hsecond : ¬({11, 15, 16} : Finset (Fin 17)) ⊆ S :=
    triangle_not_subset_of_isAcyclic S hS (by decide) (by decide) (by decide)
  obtain ⟨x, hxT, hxS⟩ := Finset.not_subset.mp hfirst
  obtain ⟨y, hyT, hyS⟩ := Finset.not_subset.mp hsecond
  have hxy : x ≠ y := by
    intro h
    subst y
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxT hyT
    rcases hxT with rfl | rfl | rfl <;> simp at hyT
  have hsubset : ({x, y} : Finset (Fin 17)) ⊆ Finset.univ \ S := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> simp [hxS, hyS]
  have hcard : 2 ≤ (Finset.univ \ S).card := by
    rw [← Finset.card_pair hxy]
    exact Finset.card_le_card hsubset
  have hpartition : (Finset.univ \ S).card + S.card = 17 := by
    simpa using Finset.card_sdiff_add_card_inter Finset.univ S
  omega

/-- The largest induced forest in the counterexample has at most $15$ vertices. -/
@[category API, AMS 5]
lemma largest_induced_forest_le_fifteen : graph.largestInducedForestSize ≤ 15 := by
  unfold largestInducedForestSize
  apply csSup_le
  · refine ⟨0, ∅, ?_, rfl⟩
    letI : Subsingleton ↥(↑(∅ : Finset (Fin 17)) : Set (Fin 17)) :=
      ⟨fun a _ => False.elim (by simpa using a.property)⟩
    exact SimpleGraph.IsAcyclic.of_subsingleton
  · rintro n ⟨S, hS, rfl⟩
    exact forest_card_le_fifteen S hS

end Counterexample

/--
WOWII [Conjecture 65](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/):

Does every simple connected graph $G$ satisfy
$f(G) \ge \operatorname{dist\_min}(A) + \lceil \operatorname{dist\_min}(M) / 3 \rceil$,
where $A$ is the set of minimum-degree vertices, $M$ is the set of maximum-degree vertices,
and $\operatorname{dist\_min}(S)$ is the minimum distance between two distinct vertices of $S$
(see `distMin`).

The answer is no. `Counterexample.graph` has a conjectured lower bound of $16$, but every
induced forest in it has at most $15$ vertices.
-/
@[category research solved, AMS 5]
theorem conjecture65 : answer(False) ↔
    ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected),
      let A : Set α := {v | G.degree v = G.minDegree}
      let M : Set α := {v | G.degree v = G.maxDegree}
      (distMin G A : ℝ) + ⌈(distMin G M : ℝ) / 3⌉ ≤
        (G.largestInducedForestSize : ℝ) := by
  constructor
  · exact False.elim
  · intro h
    have hc := h (Fin 17) Counterexample.graph Counterexample.connected
    dsimp only at hc
    rw [Counterexample.min_degree_vertices, Counterexample.max_degree_vertices,
      Counterexample.distMin_min_degree_vertices,
      Counterexample.distMin_max_degree_vertices] at hc
    have hf := Counterexample.largest_induced_forest_le_fifteen
    norm_num at hc
    exact (by omega : ¬(16 : ℕ) ≤ Counterexample.graph.largestInducedForestSize)
      (by exact_mod_cast hc)

-- Sanity checks

/-- The `largestInducedForestSize` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ G.largestInducedForestSize := Nat.zero_le _

/-- In the complete graph `K₃`, min degree equals max degree (regular graph). -/
@[category test, AMS 5]
example : (⊤ : SimpleGraph (Fin 3)).minDegree = (⊤ : SimpleGraph (Fin 3)).maxDegree := by
  decide +native

/-- `distMin G S` is always nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) (S : Set (Fin 3)) : 0 ≤ distMin G S := Nat.zero_le _

/-- In $K_2$, the minimum distance between its two vertices is $1$. -/
@[category test, AMS 5]
example : distMin (⊤ : SimpleGraph (Fin 2)) ({0, 1} : Set (Fin 2)) = 1 := by
  unfold distMin
  dsimp only
  split_ifs with h
  · rw [Finset.min'_eq_iff]
    constructor
    · refine Finset.mem_image.mpr ⟨(0, 1), ?_, ?_⟩
      · simp
      · simp
    · intro d hd
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
      have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
      simp [SimpleGraph.dist_top_of_ne hne]
  · exfalso
    apply h
    exact ⟨(0, 1), by simp⟩

/-- A singleton contains no distinct pair, so `distMin` uses its degenerate-case fallback. -/
@[category test, AMS 5]
example : distMin (⊤ : SimpleGraph (Fin 3)) ({0} : Set (Fin 3)) = 0 := by
  simp [distMin]

end WrittenOnTheWallII.GraphConjecture65
