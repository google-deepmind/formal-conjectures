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

module

public import FormalConjecturesUtil

/-!
# Written on the Wall II - Conjecture 72

**Verbatim statement (WOWII #72, status O):**
> If G is a simple connected graph, then tree(G) ≥ CEIL[average of ecc(v) + maximum of λ(v) /3]

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj72


*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Counterexample

The conjecture is false. Let `H` be the graph on `0, …, 8` with edges
`0-6, 1-6, 0-8, 1-8, 2-7, 3-7, 4-7, 2-8, 3-8, 4-8, 5-7`, and blow the vertex `5` up into a
clique `{5, 9, …, 16}` of nine vertices, all adjacent to `7`. The resulting graph `G` on
`17` vertices satisfies

* `tree(G) = 6` (only `≤ 6` is needed): two adjacent twins can only be in an induced tree on two vertices, so an
  induced tree with at least three vertices uses at most one vertex of the clique and is an
  induced tree of `H`;
* the vertex `8` has the five independent neighbours `0, …, 4`, so `max λ(v) ≥ 5`;
* the average eccentricity is `74/17` (the nine clique vertices and `6` have eccentricity `5`).

Hence `⌈74/17 + 5/3⌉ = 7 > 6 = tree(G)`. The upper bound on `tree(G)` is certified by
checking, for every vertex set `s` with at least seven vertices, that `G[s]` has the wrong
number of edges for a tree or is disconnected.
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture72

open SimpleGraph

/-- The clique `{5, 9, …, 16}` of the counterexample. -/
def inC (a : ℕ) : Bool := a == 5 || 9 ≤ a

/-- The edges of the base graph `H` (with `5` adjacent to `7`), oriented. -/
def baseRel (a b : ℕ) : Bool :=
  (a == 8 && b < 5) || (a == 6 && b < 2) || (a == 7 && 2 ≤ b && b ≤ 4)

/-- The adjacency relation of the counterexample (before symmetrisation). -/
def rel72 (a b : ℕ) : Bool :=
  baseRel a b || (inC a && inC b) || (a == 7 && inC b)

/-- The 17-vertex counterexample: the base graph `H` with the vertex `5` blown up into the
clique `{5, 9, …, 16}`, all of whose vertices are adjacent to `7`. -/
abbrev G72 : SimpleGraph (Fin 17) := SimpleGraph.fromRel (fun i j => rel72 i j = true)

instance : DecidableRel G72.Adj := fun a b =>
  decidable_of_iff (a ≠ b ∧ (rel72 a b = true ∨ rel72 b a = true)) (by simp [G72])

/-- The counterexample is connected. -/
@[category test, AMS 5]
theorem G72_connected : G72.Connected := by
  decide +native

/-- The counterexample has average eccentricity `74/17`. -/
@[category test, AMS 5]
theorem G72_averageEccentricity : averageEccentricity G72 = 74 / 17 := by
  unfold averageEccentricity
  have hsum : (∑ v : Fin 17, (G72.eccent v).toNat) = 74 := by
    simp_rw [eccent_eq_computable G72 G72_connected]
    decide +native
  rw [hsum]
  norm_num

/-- The vertex `8` has five independent neighbours. -/
@[category test, AMS 5]
theorem G72_indepNeighborsCard : 5 ≤ indepNeighborsCard G72 8 := by
  unfold indepNeighborsCard
  let t : Finset (G72.neighborSet 8) :=
    {⟨0, by rw [mem_neighborSet]; decide⟩, ⟨1, by rw [mem_neighborSet]; decide⟩,
      ⟨2, by rw [mem_neighborSet]; decide⟩, ⟨3, by rw [mem_neighborSet]; decide⟩,
      ⟨4, by rw [mem_neighborSet]; decide⟩}
  have hind : (G72.induce (G72.neighborSet 8)).IsIndepSet (t : Set (G72.neighborSet 8)) := by
    intro x hx y hy _
    simp only [t, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx hy
    rw [comap_adj, Function.Embedding.coe_subtype]
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl | rfl <;>
      decide
  have hcard : t.card = 5 := by decide
  rw [← hcard]
  exact hind.card_le_indepNum

/-! ### An upper bound for the largest induced tree -/

section TreeBound

variable {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]

omit [Fintype α] in
/-- Vertices of `s` reachable from `a` inside `s` in at most `k` steps. -/
def reachIter (s : Finset α) (a : α) : ℕ → Finset α
  | 0 => {a}
  | k + 1 => reachIter s a k ∪ s.filter (fun v => ∃ u ∈ reachIter s a k, G.Adj u v)

omit [Fintype α] in
@[category API, AMS 5]
lemma reachIter_mono (s : Finset α) (a : α) {k m : ℕ} (h : k ≤ m) :
    reachIter G s a k ⊆ reachIter G s a m := by
  induction m with
  | zero =>
    rw [Nat.le_zero.mp h]
  | succ m ih =>
    rcases Nat.lt_or_ge k (m + 1) with hk | hk
    · exact (ih (by omega)).trans Finset.subset_union_left
    · rw [show k = m + 1 by omega]

omit [Fintype α] in
@[category API, AMS 5]
lemma getVert_mem_reachIter (s : Finset α) {a b : α} (p : G.Walk a b)
    (hp : ∀ v ∈ p.support, v ∈ s) : ∀ i ≤ p.length, p.getVert i ∈ reachIter G s a i := by
  intro i
  induction i with
  | zero =>
    intro _
    simp [reachIter]
  | succ i ih =>
    intro hi
    simp only [reachIter, Finset.mem_union, Finset.mem_filter]
    refine Or.inr ⟨hp _ (p.getVert_mem_support _), p.getVert i, ih (by omega),
      p.adj_getVert_succ (by omega)⟩

@[category API, AMS 5]
lemma mem_reachIter_of_connected {s : Finset α} (hs : (G.induce (s : Set α)).Connected)
    {a b : α} (ha : a ∈ s) (hb : b ∈ s) : b ∈ reachIter G s a (Fintype.card α) := by
  obtain ⟨w⟩ := hs.preconnected ⟨a, ha⟩ ⟨b, hb⟩
  let q := w.map (Embedding.induce (G := G) (s : Set α)).toHom
  have hq : ∀ v ∈ q.support, v ∈ s := by
    intro v hv
    simp only [q, Walk.support_map, List.mem_map] at hv
    obtain ⟨x, -, rfl⟩ := hv
    exact x.2
  let p := q.bypass
  have hp : ∀ v ∈ p.support, v ∈ s := fun v hv => hq v (q.support_bypass_subset_support hv)
  have hlen : p.length < Fintype.card α := q.bypass_isPath.length_lt
  have h1 := getVert_mem_reachIter G s p hp p.length le_rfl
  rw [Walk.getVert_length] at h1
  exact reachIter_mono G s a hlen.le h1

@[category API, AMS 5]
lemma card_edges_of_isTree {s : Finset α} (hT : (G.induce (s : Set α)).IsTree) :
    (G.edgeFinset ∩ s.sym2).card + 1 = s.card := by
  have h1 := hT.card_edgeFinset
  have h2 := congrArg Finset.card (map_edgeFinset_induce (G := G) (s := (s : Set α)))
  rw [Finset.card_map, Finset.toFinset_coe] at h2
  have h3 : Fintype.card (s : Set α) = s.card := by simp
  rw [← h2, ← h3]
  convert h1

end TreeBound

/-- Certificate: no vertex set of size at least seven induces a tree in `G72`. -/
@[category test, AMS 5]
theorem G72_certificate : ∀ s : Finset (Fin 17), 7 ≤ s.card →
    (G72.edgeFinset ∩ s.sym2).card + 1 = s.card →
    ∃ a ∈ s, ∃ b ∈ s, b ∉ reachIter G72 s a 17 := by
  decide +native

/-- The largest induced tree of `G72` has at most six vertices. -/
@[category test, AMS 5]
theorem G72_largestInducedTreeSize_le : largestInducedTreeSize G72 ≤ 6 := by
  unfold largestInducedTreeSize
  apply csSup_le
  · refine ⟨1, {0}, rfl, ?_⟩
    rw [Finset.coe_singleton]
    have : Unique ({0} : Set (Fin 17)) := Set.uniqueSingleton 0
    exact IsTree.of_subsingleton
  · rintro n ⟨s, rfl, hT⟩
    by_contra hlt
    push Not at hlt
    have hc := card_edges_of_isTree G72 hT
    obtain ⟨a, ha, b, hb, hab⟩ := G72_certificate s hlt hc
    have hr := mem_reachIter_of_connected G72 hT.connected ha hb
    rw [Fintype.card_fin] at hr
    exact hab hr

/--
WOWII [Conjecture 72](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`,
$\operatorname{tree}(G) ≥ ⌈\operatorname{ecc}_{\mathrm{avg}}(G) + \max_v \lambda(v)/3⌉$
where `tree(G)` is the number of vertices in a largest induced tree,
`ecc_avg(G)` is the average eccentricity of `G`, and
`max_v l(v) = max_v indepNeighborsCard G v` is the maximum over all vertices of
the independence number of the neighbourhood.

This conjecture is false: for the 17-vertex graph `G72` we have `tree = 6`,
`ecc_avg = 74/17` and `max λ ≥ 5`, so the right-hand side is at least `7`.
-/
@[category research solved, AMS 5]
theorem conjecture72 : ¬ ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
    (G : SimpleGraph α) (_h : G.Connected),
    let maxL := (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp)
    ⌈averageEccentricity G + (maxL : ℝ) / 3⌉ ≤ (largestInducedTreeSize G : ℝ) := by
  intro h
  have hbad := h (Fin 17) G72 G72_connected
  simp only at hbad
  rw [G72_averageEccentricity] at hbad
  set maxL := (Finset.univ.image (fun v => indepNeighborsCard G72 v)).max' (by simp)
  have hL : 5 ≤ maxL := G72_indepNeighborsCard.trans
    (Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ 8)))
  have ht : (largestInducedTreeSize G72 : ℝ) ≤ 6 := by
    exact_mod_cast G72_largestInducedTreeSize_le
  have hL' : (5 : ℝ) ≤ maxL := by exact_mod_cast hL
  have hceil : (6 : ℤ) < ⌈(74 / 17 : ℝ) + (maxL : ℝ) / 3⌉ := by
    rw [Int.lt_ceil]
    push_cast
    linarith
  have h7 : (7 : ℝ) ≤ (⌈(74 / 17 : ℝ) + (maxL : ℝ) / 3⌉ : ℝ) := by
    exact_mod_cast hceil
  linarith

-- Sanity checks

/-- The `largestInducedTreeSize` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ largestInducedTreeSize G := Nat.zero_le _

/-- The average eccentricity is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ averageEccentricity G := by
  unfold averageEccentricity
  positivity

end WrittenOnTheWallII.GraphConjecture72
