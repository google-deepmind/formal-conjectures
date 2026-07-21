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
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.VertexDistance
public import Mathlib.Combinatorics.SimpleGraph.Diam

@[expose] public section

/-!
# Metric of a graph square

For a connected graph `G`, this file proves

`dist_(G²)(u,v) = ⌈dist_G(u,v) / 2⌉ = (dist_G(u,v) + 1) / 2`.

The proof is split into two directions. A walk in the square expands to at
most two original edges per step. Conversely, a shortest original walk is
compressed two edges at a time.
-/

namespace SimpleGraph

open Classical

variable {α : Type*}
variable {G : SimpleGraph α}

/-- Every original edge is an edge of the square graph. -/
lemma adj_graphSquare_of_adj {u v : α} (h : G.Adj u v) :
    (graphSquare G).Adj u v := by
  refine ⟨G.ne_of_adj h, ?_⟩
  exact (G.dist_le (Walk.cons h Walk.nil)).trans (by norm_num)

/-- Squaring a connected graph preserves connectedness. -/
lemma Connected.graphSquare (hG : G.Connected) : (graphSquare G).Connected := by
  exact hG.mono fun _ _ h => adj_graphSquare_of_adj h

/-- A walk of length `m` in `G²` expands to a route of length at most `2m` in `G`. -/
private lemma dist_le_two_mul_length_of_graphSquare_walk
    (hG : G.Connected) {u v : α} (p : (graphSquare G).Walk u v) :
    G.dist u v ≤ 2 * p.length := by
  induction p with
  | nil => simp
  | @cons u w v huw p ih =>
      have htri := hG.dist_triangle (u := u) (v := w) (w := v)
      have huw' : G.dist u w ≤ 2 := huw.2
      simp only [Walk.length_cons]
      omega

/-- The original distance is at most twice the square-graph distance. -/
lemma dist_le_two_mul_graphSquare_dist (hG : G.Connected) (u v : α) :
    G.dist u v ≤ 2 * (graphSquare G).dist u v := by
  obtain ⟨p, hp⟩ := hG.graphSquare.exists_walk_length_eq_dist u v
  rw [← hp]
  exact dist_le_two_mul_length_of_graphSquare_walk hG p

/-- Lower half of the graph-square distance formula. -/
lemma half_dist_le_graphSquare_dist (hG : G.Connected) (u v : α) :
    (G.dist u v + 1) / 2 ≤ (graphSquare G).dist u v := by
  have h := dist_le_two_mul_graphSquare_dist hG u v
  omega

/-- Compress an original walk two steps at a time to bound distance in `G²`. -/
private lemma graphSquare_dist_le_half_walk
    (hG : G.Connected) {u v : α} (p : G.Walk u v) :
    (graphSquare G).dist u v ≤ (p.length + 1) / 2 := by
  induction hn : p.length using Nat.strong_induction_on generalizing u v p with
  | h n ih =>
      cases p with
      | nil => simp
      | @cons u x v hux q =>
          cases q with
          | nil =>
              have hs : (graphSquare G).Adj u v := adj_graphSquare_of_adj hux
              rw [dist_eq_one_iff_adj.mpr hs]
              simp at hn
              omega
          | @cons x y v hxy r =>
              have hrlt : r.length < n := by
                simp only [Walk.length_cons] at hn
                omega
              have hir := ih r.length hrlt (p := r) rfl
              have htwo : G.dist u y ≤ 2 := by
                exact (G.dist_le (Walk.cons hux (Walk.cons hxy Walk.nil))).trans
                  (by norm_num)
              by_cases huy : u = y
              · subst y
                simp only [Walk.length_cons] at hn ⊢
                omega
              · have hs : (graphSquare G).Adj u y := ⟨huy, htwo⟩
                have htri := hG.graphSquare.dist_triangle (u := u) (v := y) (w := v)
                have hdistuy : (graphSquare G).dist u y = 1 :=
                  dist_eq_one_iff_adj.mpr hs
                rw [hdistuy] at htri
                simp only [Walk.length_cons] at hn ⊢
                omega

/-- Upper half of the graph-square distance formula. -/
lemma graphSquare_dist_le_half (hG : G.Connected) (u v : α) :
    (graphSquare G).dist u v ≤ (G.dist u v + 1) / 2 := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist u v
  simpa [hp] using graphSquare_dist_le_half_walk hG p

/-- Distance in the graph square is the ceiling of half the original distance. -/
theorem graphSquare_dist (hG : G.Connected) (u v : α) :
    (graphSquare G).dist u v = (G.dist u v + 1) / 2 := by
  exact le_antisymm (graphSquare_dist_le_half hG u v)
    (half_dist_le_graphSquare_dist hG u v)


end SimpleGraph
