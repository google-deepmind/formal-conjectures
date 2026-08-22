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

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

open Finset List

/--
Two walks are internally disjoint if they share no vertices other than their endpoints.
-/
def InternallyDisjoint {u v x y : V} (p : G.Walk u v) (q : G.Walk x y) : Prop :=
  Disjoint p.support.tail.dropLast q.support.tail.dropLast

/--
We say a graph is infinitely connected if any two vertices are connected by infinitely many
pairwise disjoint paths. Note that graphs with at most one vertex are not classed as
infinitely connected.
-/
def InfinitelyConnected (G : SimpleGraph V) : Prop := Nontrivial V ∧
  Pairwise fun u v ↦ ∃ P : Set (G.Walk u v),
    P.Infinite ∧ (∀ p ∈ P, p.IsPath) ∧ P.Pairwise InternallyDisjoint

/-- `G` is `k`-connected: it has more than `k` vertices, and it stays connected after the
removal of any set of fewer than `k` vertices.

Mathlib has `SimpleGraph.IsEdgeConnected`, but it has no vertex connectivity. -/
def IsKConnected {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧ ∀ S : Finset V, S.card < k → (G.induce ((S : Set V)ᶜ)).Connected

/-- A graph on at most `k` vertices is not `k`-connected. -/
theorem not_isKConnected_of_card_le {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (h : Fintype.card V ≤ k) : ¬ IsKConnected G k :=
  fun hG => absurd hG.1 (not_lt.mpr h)

/-!
### Deciding reachability by breadth-first search

This section provides efficient decidability instances for reachability and (pre)connectedness of
finite graphs through a breadth-first search (BFS) algorithm.

The algorithm is as follows: we maintain a finset of visited vertices which we grow with all its
neighbors at each round of breadth-first search at, stopping as soon as a round adds no new vertex:
a search costs `O((diam G + 1) * (card V) ^ 2)` adjacency tests.

Vertices `u` and `v` are then reachable if `v` lies in the BFS-constructed finset of vertices
reachable from `u`, and a graph is (pre)connected iff it's non-empty and (/empty or) every vertex is
lies in the reachability finset of an arbitrarily-chosen vertex.
-/

section BFS
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {m n : ℕ} {s t : Finset V} {u v w : V}

variable (G s) in
/-- One round of breadth-first search: `G.bfsStep s` consists of the vertices of `s` together with
their neighbours. -/
def bfsStep : Finset V := {w | w ∈ s ∨ ∃ v ∈ s, G.Adj v w}

@[simp, grind =]
lemma mem_bfsStep : w ∈ G.bfsStep s ↔ w ∈ s ∨ ∃ v ∈ s, G.Adj v w := by simp [bfsStep]

lemma subset_bfsStep : s ⊆ G.bfsStep s := fun _ hw ↦ G.mem_bfsStep.2 <| .inl hw

@[gcongr] lemma bfsStep_mono (hst : s ⊆ t) : G.bfsStep s ⊆ G.bfsStep t := by grind

@[gcongr]
lemma iterate_bfsStep_mono (hst : s ⊆ t) : G.bfsStep^[n] s ⊆ G.bfsStep^[n] t := by
  induction n generalizing s t with
  | zero => exact hst
  | succ n ih => simpa only [Function.iterate_succ_apply] using ih (G.bfsStep_mono hst)

lemma subset_iterate_bfsStep : s ⊆ G.bfsStep^[n] s := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih => grw [Function.iterate_succ_apply', ← ih, ← G.subset_bfsStep]

lemma iterate_bfsStep_subset_of_le (hmn : m ≤ n) : G.bfsStep^[m] s ⊆ G.bfsStep^[n] s := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [Function.iterate_add_apply]
  exact G.iterate_bfsStep_mono G.subset_iterate_bfsStep

lemma mem_iterate_bfsStep_of_walk (p : G.Walk u v) : v ∈ G.bfsStep^[p.length] {u} := by
  induction p with
  | nil => simp
  | cons h p ih =>
    rw [Walk.length_cons, Function.iterate_succ_apply]
    exact G.iterate_bfsStep_mono (by simp [h]) ih

lemma reachable_of_mem_iterate_bfsStep (hv : v ∈ G.bfsStep^[n] {u}) : G.Reachable u v := by
  induction n generalizing v with
  | zero =>
    rw [Function.iterate_zero_apply, Finset.mem_singleton] at hv
    exact hv ▸ Reachable.refl _
  | succ n ih =>
    rw [Function.iterate_succ_apply', mem_bfsStep] at hv
    obtain hv | ⟨w, hw, hwv⟩ := hv
    · exact ih hv
    · exact (ih hw).trans hwv.reachable

/-- Iterate `G.bfsStep` at most `n` times, stopping as soon as no new vertex shows up. -/
def bfsIterate : ℕ → Finset V → Finset V
  | 0, s => s
  | n + 1, s => if (G.bfsStep s).card ≤ s.card then s else bfsIterate n (G.bfsStep s)

lemma bfsIterate_eq_iterate_bfsStep (n : ℕ) (s : Finset V) :
    G.bfsIterate n s = G.bfsStep^[n] s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [bfsIterate]
    split_ifs with h
    · have hs : G.bfsStep s = s := (Finset.eq_of_subset_of_card_le G.subset_bfsStep h).symm
      exact (Function.iterate_fixed hs _).symm
    · rw [ih, ← Function.iterate_succ_apply]

/-- The finset of vertices reachable from `u`, computed by breadth-first search. -/
def reachableFinset (u : V) : Finset V := G.bfsIterate (Fintype.card V) {u}

@[simp]
lemma mem_reachableFinset : v ∈ G.reachableFinset u ↔ G.Reachable u v := by
  rw [reachableFinset, bfsIterate_eq_iterate_bfsStep]
  refine ⟨G.reachable_of_mem_iterate_bfsStep, fun h ↦ h.elim_path fun p ↦ ?_⟩
  exact G.iterate_bfsStep_subset_of_le p.2.length_lt.le (G.mem_iterate_bfsStep_of_walk p.1)

/-- Decides reachability of vertices `u` and `v` by performing a breadth-first search from `u`. -/
instance decidableReachable : DecidableRel G.Reachable :=
  fun _ _ ↦ decidable_of_iff _ G.mem_reachableFinset

lemma preconnected_iff_forall_mem_reachableFinset (u : V) :
    G.Preconnected ↔ ∀ v, v ∈ G.reachableFinset u := by
  simp only [mem_reachableFinset]
  exact ⟨fun h v ↦ h u v, fun h x y ↦ (h x).symm.trans (h y)⟩

/-- Decides preconnectedness of `G` by checking whether the vertex set is empty and, if not,
by performing a breadth-first search from an arbitrarily chosen vertex. -/
instance decidablePreconnected : Decidable G.Preconnected :=
  if h : Fintype.card V = 0 then
    isTrue (by rw [Fintype.card_eq_zero_iff] at h; exact .of_subsingleton)
  else
    (truncOfCardPos <| by lia).lift
      (fun u ↦ decidable_of_iff _ (G.preconnected_iff_forall_mem_reachableFinset u).symm)
      fun _ _ ↦ Subsingleton.elim _ _

lemma connected_iff_forall_mem_reachableFinset (u : V) :
    G.Connected ↔ ∀ v, v ∈ G.reachableFinset u := by
  rw [connected_iff, G.preconnected_iff_forall_mem_reachableFinset u, and_iff_left ⟨u⟩]

/-- Decides preconnectedness of `G` by checking whether the vertex set is empty and, if not,
by performing a breadth-first search from an arbitrarily chosen vertex. -/
instance decidableConnected : Decidable G.Connected :=
  if h : Fintype.card V = 0 then
    isFalse fun hG ↦ (Fintype.card_eq_zero_iff.1 h).false hG.nonempty.some
  else
    (truncOfCardPos <| by lia).lift
      (fun u ↦ decidable_of_iff _ (G.connected_iff_forall_mem_reachableFinset u).symm)
      fun _ _ ↦ Subsingleton.elim ..

end BFS
end SimpleGraph
