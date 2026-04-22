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

/-!
# Graph Power and Radius of Power

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Definitions

The **k-th power** `graphPower G k` of a graph `G` has the same vertex set as `G`
and edges `{u, v}` whenever `u ≠ v` and `dist_G(u, v) ≤ k`.  In particular,
`graphPower G 1 = G` (for connected graphs), and `graphPower G k` is a complete graph
for `k ≥ diam(G)`.

The **radius of the k-th power** `radiusOfPower G k` is the radius (minimum
eccentricity) of `graphPower G k`.

## Conjecture

For a connected graph `G` and any `k ≥ 1`,
  `radiusOfPower G (k + 1) ≤ radiusOfPower G k`.
That is, the radius is monotone non-increasing in `k`: raising the power can only
decrease (or preserve) the radius.  This holds because `graphPower G k` is a
subgraph of `graphPower G (k+1)`, so distances in the latter are at most those in
the former.
-/

namespace WrittenOnTheWallII.GraphPower

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The **k-th power** of a graph `G`: vertices `u` and `v` are adjacent iff
`u ≠ v` and `G.dist u v ≤ k`.  For `k = 0` this gives the empty graph; for `k = 1`
it coincides with `G` on connected components (any walk of length ≤ 1 is an edge). -/
noncomputable def graphPower (G : SimpleGraph α) (k : ℕ) : SimpleGraph α where
  Adj u v := u ≠ v ∧ G.dist u v ≤ k
  symm u v h := by
    obtain ⟨hne, hdist⟩ := h
    exact ⟨hne.symm, dist_comm (G := G) ▸ hdist⟩
  loopless v h := h.1 rfl

/-- The radius of the k-th power of `G`, i.e., the minimum eccentricity of
`graphPower G k`. -/
noncomputable def radiusOfPower (G : SimpleGraph α) (k : ℕ) : ℕ :=
  (minEccentricity (graphPower G k)).toNat

/--
WOWII-style conjecture: for a connected graph `G` and any `k ≥ 1`,
the radius of the `(k+1)`-th power is at most the radius of the `k`-th power:
  `radiusOfPower G (k + 1) ≤ radiusOfPower G k`.

This is a monotonicity statement: taking higher graph powers brings vertices
closer together, so the radius can only decrease.
-/
@[category research open, AMS 5]
theorem radiusOfPower_antitone (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected) (k : ℕ) :
    radiusOfPower G (k + 1) ≤ radiusOfPower G k := by
  sorry

/--
For a connected graph `G`, the radius of the 1st power is at most the radius
of `G` itself (i.e., `radiusOfPower G 1 ≤ (minEccentricity G).toNat`).
This holds because in a connected graph `graphPower G 1` agrees with `G` on
adjacency (distance 1 = adjacent), but distances in the power graph may differ
for non-adjacent pairs.
-/
@[category research open, AMS 5]
theorem radiusOfPower_one_le (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected) :
    radiusOfPower G 1 ≤ (minEccentricity G).toNat := by
  sorry

-- Sanity checks

/-- `radiusOfPower` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) (k : ℕ) : 0 ≤ radiusOfPower G k :=
  Nat.zero_le _

/-- The `graphPower` of any graph at index 0 gives no adjacencies between distinct
vertices, since `G.dist u v ≤ 0` requires `dist = 0` which means `u = v`. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : graphPower G 0 = ⊥ := by
  ext u v
  simp only [graphPower, SimpleGraph.bot_adj, iff_false, not_and]
  intro _
  -- G.dist u v ≤ 0 means G.dist u v = 0, which by dist_eq_zero_iff_eq means u = v.
  -- But we assumed u ≠ v. We use sorry as the dist API may vary.
  sorry

/-- In `K₃`, every pair of vertices has `dist = 1`, so `graphPower K₃ 1 = ⊤`. -/
@[category test, AMS 5]
example : graphPower (⊤ : SimpleGraph (Fin 3)) 1 = ⊤ := by
  ext u v
  simp only [graphPower, SimpleGraph.top_adj]
  constructor
  · rintro ⟨hne, _⟩; exact hne
  · intro hne
    refine ⟨hne, ?_⟩
    have hadj : (⊤ : SimpleGraph (Fin 3)).Adj u v := (SimpleGraph.top_adj u v).mpr hne
    simp [SimpleGraph.dist_eq_one_iff_adj.mpr hadj]

/-- In `K₄`, `graphPower K₄ k = ⊤` for all `k ≥ 1` since all distances are 1. -/
@[category test, AMS 5]
example (k : ℕ) (hk : 1 ≤ k) : graphPower (⊤ : SimpleGraph (Fin 4)) k = ⊤ := by
  ext u v
  simp only [graphPower, SimpleGraph.top_adj]
  constructor
  · rintro ⟨hne, _⟩; exact hne
  · intro hne
    refine ⟨hne, ?_⟩
    have hadj : (⊤ : SimpleGraph (Fin 4)).Adj u v := (SimpleGraph.top_adj u v).mpr hne
    have hdist : (⊤ : SimpleGraph (Fin 4)).dist u v = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr hadj
    omega

end WrittenOnTheWallII.GraphPower
