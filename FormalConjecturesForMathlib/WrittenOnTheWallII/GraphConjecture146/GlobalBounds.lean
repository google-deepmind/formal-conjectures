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
public import FormalConjecturesForMathlib.WrittenOnTheWallII.GraphConjecture146.GraphSquareRadius
public import FormalConjecturesForMathlib.WrittenOnTheWallII.GraphConjecture142Proof
public import Mathlib.Combinatorics.SimpleGraph.Hasse

@[expose] public section

/-!
# Global bounds for WOWII Conjecture 146

This module packages the induced-geodesic, periphery, and radius/diameter
estimates used in the arithmetic reduction of Conjecture 146.
-/

namespace SimpleGraph

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
variable {G : SimpleGraph α}

omit [Fintype α] [Nontrivial α] in
/-- The support of a distance-realizing walk induces a tree. -/
lemma Walk.induce_support_toFinset_isTree_of_length_eq_dist
    {u v : α} (p : G.Walk u v) (hp : p.length = G.dist u v) :
    (G.induce (p.support.toFinset : Set α)).IsTree := by
  induction p with
  | @nil u =>
      have hset :
          (↑(Walk.nil : G.Walk u u).support.toFinset : Set α) = {u} := by
        ext x
        simp
      rw [hset]
      letI : Nonempty ↥({u} : Set α) := ⟨⟨u, by simp⟩⟩
      letI : Subsingleton ↥({u} : Set α) := ⟨fun a b => by
        apply Subtype.ext
        simpa only [Set.mem_singleton_iff] using a.property.trans b.property.symm⟩
      exact IsTree.of_subsingleton
  | @cons u v w huv p ih =>
      have hptail : p.length = G.dist v w :=
        length_eq_dist_of_subwalk hp (Walk.isSubwalk_cons p huv)
      have htree := ih hptail
      have hfullPath := (p.cons huv).isPath_of_length_eq_dist hp
      have huNot : u ∉ p.support.toFinset := by
        simpa using (List.nodup_cons.mp hfullPath.support_nodup).1
      have huniq : ∀ ⦃b : α⦄, b ∈ p.support.toFinset → G.Adj u b → b = v := by
        intro b hb hub
        have hbSupport : b ∈ (p.cons huv).support := by
          simp only [Walk.support_cons, List.mem_cons]
          exact Or.inr (by simpa using hb)
        have hedge := (p.cons huv).chordless_of_length_eq_dist hp
          (by simp) hbSupport hub
        simpa using hfullPath.eq_snd_of_mem_edges hedge
      have hsupp : (Walk.cons huv p).support.toFinset =
          insert u p.support.toFinset := by simp
      rw [hsupp]
      exact htree.induce_insert_of_unique_adj huNot (by simp) huv huniq

omit [DecidableEq α] [Nontrivial α] in
/-- Every explicit finite induced tree is bounded by the largest induced-tree order. -/
lemma finset_card_le_largestInducedTreeSize {s : Finset α}
    (hs : (G.induce (s : Set α)).IsTree) :
    s.card ≤ largestInducedTreeSize G :=
  hs.card_le_largestInducedTreeSize_splice

/-- A diametral geodesic supplies an induced tree on `diam + 1` vertices. -/
lemma diam_succ_le_largestInducedTreeSize (hG : G.Connected) :
    G.diam + 1 ≤ largestInducedTreeSize G :=
  diam_add_one_le_largestInducedTreeSize_splice hG

omit [DecidableEq α] in
/-- The eccentricity of the peripheral set is strictly below the diameter. -/
lemma eccSet_periphery_add_one_le_diam (hG : G.Connected) :
    eccSet G (maxEccentricityVertices G : Set α) + 1 ≤ G.diam := by
  by_cases hp : eccSet G (maxEccentricityVertices G : Set α) = 0
  · have hd : G.diam ≠ 0 := (connected_iff_diam_ne_zero).mp hG
    omega
  · exact eccSet_maxEccentricityVertices_add_one_le_diam_splice hG
      (Nat.pos_of_ne_zero hp)

omit [DecidableEq α] in
/-- In a finite connected graph, the natural-valued radius is at most the diameter. -/
lemma radius_toNat_le_diam (hG : G.Connected) :
    G.radius.toNat ≤ G.diam := by
  have hed : G.ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hG
  unfold diam
  exact ENat.toNat_le_toNat radius_le_ediam hed

omit [DecidableEq α] in
/-- In a finite connected graph, the diameter is at most twice the natural-valued radius. -/
lemma diam_le_two_mul_radius_toNat (hG : G.Connected) :
    G.diam ≤ 2 * G.radius.toNat := by
  have hr : G.radius ≠ ⊤ := radius_ne_top_iff.mpr hG
  have hmul : (2 : ℕ∞) * G.radius ≠ ⊤ :=
    WithTop.mul_ne_top (ENat.coe_ne_top 2) hr
  have h := ENat.toNat_le_toNat (ediam_le_two_mul_radius (G := G)) hmul
  simpa [diam] using h

section Regression

/-- Path regression: the five-vertex path is connected. -/
example : (pathGraph 5).diam + 1 ≤ largestInducedTreeSize (pathGraph 5) := by
  apply diam_succ_le_largestInducedTreeSize
  simpa using pathGraph_connected 4

/-- Cycle regression: the triangle is the complete graph on three vertices. -/
example :
    eccSet (⊤ : SimpleGraph (Fin 3))
        (maxEccentricityVertices (⊤ : SimpleGraph (Fin 3)) : Set (Fin 3)) + 1 ≤
      (⊤ : SimpleGraph (Fin 3)).diam :=
  eccSet_periphery_add_one_le_diam connected_top

/-- Complete-graph regression. -/
example : (⊤ : SimpleGraph (Fin 4)).radius.toNat ≤ (⊤ : SimpleGraph (Fin 4)).diam :=
  radius_toNat_le_diam connected_top

/-- Star regression: the three-vertex path is the star `K₁,₂`. -/
example : (pathGraph 3).diam ≤ 2 * (pathGraph 3).radius.toNat := by
  apply diam_le_two_mul_radius_toNat
  simpa using pathGraph_connected 2

end Regression


end SimpleGraph
