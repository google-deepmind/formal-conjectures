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
public import FormalConjecturesForMathlib.WrittenOnTheWallII.GraphConjecture146.GlobalBounds

@[expose] public section

/-!
# Metric lemmas for WOWII Conjecture 146

The square-graph radius-one case supplies a vertex at original distance at
most two from every vertex. This module also packages the short-geodesic and
short-walk facts used by the exceptional induced-tree construction.
-/

open Classical
open SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture146.Proof

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- Every edge of `G` is an edge of its square, so connectedness is preserved. -/
lemma connected_graphSquare (G : SimpleGraph α) (hG : G.Connected) :
    (graphSquare G).Connected := by
  refine hG.mono ?_
  intro u v huv
  refine ⟨G.ne_of_adj huv, ?_⟩
  exact (G.dist_le (.cons huv .nil)).trans (by norm_num)

/-- Square-graph distance at most one implies original distance at most two. -/
lemma dist_le_two_of_graphSquare_dist_le_one (G : SimpleGraph α) (hG : G.Connected)
    {u v : α} (h : (graphSquare G).dist u v ≤ 1) : G.dist u v ≤ 2 := by
  by_cases huv : u = v
  · subst v
    simp
  · have hsconn : (graphSquare G).Connected := connected_graphSquare G hG
    have hpos : 0 < (graphSquare G).dist u v := hsconn.pos_dist_of_ne huv
    have hdist : (graphSquare G).dist u v = 1 := by omega
    exact (dist_eq_one_iff_adj.mp hdist).2

/-- A radius-one square graph has a center whose original distance to every
vertex is at most two. -/
lemma exists_square_center_original_dist_le_two (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) (hrho : (graphSquare G).radius.toNat = 1) :
    ∃ c : α, ∀ v : α, G.dist c v ≤ 2 := by
  have hsconn : (graphSquare G).Connected := connected_graphSquare G hG
  obtain ⟨c, hc⟩ := (graphSquare G).exists_eccent_eq_radius
  have hrfin : (graphSquare G).radius ≠ ⊤ := radius_ne_top_iff.mpr hsconn
  have hefin : (graphSquare G).eccent c ≠ ⊤ := by
    rw [hc]
    exact hrfin
  refine ⟨c, fun v => ?_⟩
  apply dist_le_two_of_graphSquare_dist_le_one G hG
  change ((graphSquare G).edist c v).toNat ≤ 1
  calc
    ((graphSquare G).edist c v).toNat ≤ ((graphSquare G).eccent c).toNat :=
      ENat.toNat_le_toNat edist_le_eccent hefin
    _ = ((graphSquare G).radius).toNat := congrArg ENat.toNat hc
    _ = (graphSquare G).radius.toNat := rfl
    _ = 1 := hrho

/-- If the square graph has natural radius one, then `G` has diameter at most four. -/
lemma diam_le_four_of_graphSquareRadius_eq_one (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) (hrho : (graphSquare G).radius.toNat = 1) : G.diam ≤ 4 := by
  obtain ⟨c, hc⟩ := exists_square_center_original_dist_le_two G hG hrho
  obtain ⟨u, v, huv⟩ := G.exists_dist_eq_diam
  rw [← huv]
  calc
    G.dist u v ≤ G.dist u c + G.dist c v := hG.dist_triangle
    _ ≤ 2 + 2 := Nat.add_le_add (by simpa [dist_comm] using hc u) (hc v)
    _ = 4 := by norm_num

/-- A pair at distance two has a common intermediate neighbor. -/
lemma exists_middle_of_dist_eq_two (G : SimpleGraph α) (hG : G.Connected)
    {u v : α} (huv : G.dist u v = 2) :
    ∃ w : α, G.Adj u w ∧ G.Adj w v := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist u v
  have hlen : p.length = 2 := hp.trans huv
  let w := p.getVert 1
  refine ⟨w, ?_, ?_⟩
  · have h := p.adj_getVert_succ (show 0 < p.length by omega)
    simpa [w] using h
  · have h := p.adj_getVert_succ (show 1 < p.length by omega)
    have hlast : p.getVert 2 = v := by simpa [hlen] using p.getVert_length
    rw [hlast] at h
    simpa [w] using h

/-- A pair at distance three has a three-edge geodesic with two internal vertices. -/
lemma exists_two_middle_of_dist_eq_three (G : SimpleGraph α) (hG : G.Connected)
    {u v : α} (huv : G.dist u v = 3) :
    ∃ b a : α, G.Adj u b ∧ G.Adj b a ∧ G.Adj a v := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist u v
  have hlen : p.length = 3 := hp.trans huv
  let b := p.getVert 1
  let a := p.getVert 2
  refine ⟨b, a, ?_, ?_, ?_⟩
  · have h := p.adj_getVert_succ (show 0 < p.length by omega)
    simpa [b] using h
  · have h := p.adj_getVert_succ (show 1 < p.length by omega)
    simpa [b, a] using h
  · have h := p.adj_getVert_succ (show 2 < p.length by omega)
    have hlast : p.getVert 3 = v := by simpa [hlen] using p.getVert_length
    rw [hlast] at h
    simpa [a] using h

lemma dist_le_two_of_adj_adj (G : SimpleGraph α) {a b c : α}
    (hab : G.Adj a b) (hbc : G.Adj b c) : G.dist a c ≤ 2 := by
  simpa using G.dist_le (.cons hab (.cons hbc .nil))

lemma dist_le_three_of_adj_adj_adj (G : SimpleGraph α) {a b c d : α}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) : G.dist a d ≤ 3 := by
  simpa using G.dist_le (.cons hab (.cons hbc (.cons hcd .nil)))

lemma dist_le_four_of_adj_adj_adj_adj (G : SimpleGraph α) {a b c d e : α}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hde : G.Adj d e) :
    G.dist a e ≤ 4 := by
  simpa using G.dist_le (.cons hab (.cons hbc (.cons hcd (.cons hde .nil))))

/-- Vertices at distance at least two are nonadjacent. -/
lemma not_adj_of_two_le_dist (G : SimpleGraph α) {u v : α} (h : 2 ≤ G.dist u v) :
    ¬G.Adj u v := by
  intro huv
  have hdist : G.dist u v = 1 := dist_eq_one_iff_adj.mpr huv
  omega

end WrittenOnTheWallII.GraphConjecture146.Proof
