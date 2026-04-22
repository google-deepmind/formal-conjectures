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
# Graph Length (Sum of Eccentricities) Conjecture

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Definitions

The **length** of a graph `G`, in DeLaVina's WOWII notation, refers to the
**sum of eccentricities** over all vertices:
  `length(G) = ∑_v ecc(v)`.

This is distinct from the diameter (maximum eccentricity) and the Wiener index
(sum of pairwise distances).  For a connected graph on `n` vertices:
- `length(G) ≥ n · radius(G)` (each vertex has eccentricity ≥ radius), and
- `length(G) ≤ n · diameter(G)` (each eccentricity ≤ diameter).

## Conjecture

WOWII Conjecture 19 uses `length(G)` as the sum of eccentricities.  We state a
Graffiti.pc-style lower bound:

`α(G) ≤ ⌊length(G) / n + max_v l(v)⌋`

where `α(G)` is the independence number, `n = |V(G)|`, `l(v)` is the
independence number of the neighbourhood of `v`, and the floor is taken in ℝ.
-/

namespace WrittenOnTheWallII.GraphLength

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The **length** of `G`: sum of eccentricities over all vertices.
Each eccentricity is in `ℕ∞`; we convert to `ℕ` via `.toNat`
(which returns 0 for the `⊤` case, i.e., when the graph is disconnected). -/
noncomputable def graphLength (G : SimpleGraph α) : ℕ :=
  ∑ v : α, (eccentricity G v).toNat

/--
**Length-based independence bound** (WOWII-style conjecture).

For a connected graph `G` on `n` vertices,
`α(G) ≤ ⌊length(G) / n + max_v l(v)⌋`
where `length(G) = ∑_v ecc(v)` is the sum of eccentricities,
`n = Fintype.card α`, and `l(v) = indepNeighborsCard G v` is the
independence number of the neighbourhood of `v`.

This refines the well-known bound `α(G) ≤ max_v l(v)` by adding the average
eccentricity.
-/
@[category research open, AMS 5]
theorem graphLength_indepNum_upper_bound (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected) :
    let len := graphLength G
    let n   := Fintype.card α
    let maxL := (Finset.univ.image (indepNeighborsCard G)).max' (by simp)
    (G.indepNum : ℝ) ≤
      ⌊(len : ℝ) / (n : ℝ) + (maxL : ℝ)⌋ := by
  sorry

-- Sanity checks

/-- `graphLength` is a natural number (nonneg). -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ graphLength G := Nat.zero_le _

/-- For `K₃` every vertex has eccentricity 1, so `graphLength K₃ = 3`. -/
@[category test, AMS 5]
example : graphLength (⊤ : SimpleGraph (Fin 3)) = 3 := by
  unfold graphLength eccentricity
  sorry

/-- `graphLength` of any graph is nonneg as a real. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) : (0 : ℝ) ≤ (graphLength G : ℝ) :=
  Nat.cast_nonneg _

end WrittenOnTheWallII.GraphLength
