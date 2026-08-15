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

import FormalConjecturesUtil

/-!
# Graph Crossing Number

*Reference:*
[M. R. Garey and D. S. Johnson, Crossing number is NP-complete, SIAM J. Algebraic Discrete
Methods 4 (1983) 312–316](https://doi.org/10.1137/0604033)

[R. B. Richter and C. Thomassen, Minimal graphs with crossing number at least k,
J. Combin. Theory Ser. B 58 (1993) 217–224]

[F. T. Leighton, Complexity issues in VLSI, MIT Press, 1983]

## Definition

The **crossing number** `cr(G)` of a graph `G` is the minimum number of edge
crossings over all drawings of `G` in the plane (where vertices map to distinct
points and edges to Jordan arcs between their endpoints, with only finitely many
pairwise crossings, each transverse and not at a vertex).

A full geometric formalization of this definition requires substantial topological
infrastructure.  We use a placeholder definition here.

-- TODO: replace `Classical.choice` with a proper topological definition once
-- Mathlib has sufficient support for planar graph drawings (Jordan curves, etc.).

## Conjecture

**Zarankiewicz's conjecture** (1954) — **open**:
  `cr(K_{m,n}) = ⌊m/2⌋ · ⌊(m−1)/2⌋ · ⌊n/2⌋ · ⌊(n−1)/2⌋`.

The formula gives the number of crossings in the standard "cylindrical" drawing
of the complete bipartite graph `K_{m,n}`.  The conjecture is known to hold for
`min(m, n) ≤ 6` but remains open in general.
-/

namespace WrittenOnTheWallII.GraphCrossingNumber

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The **crossing number** of a graph `G`: the minimum number of edge crossings
in any planar drawing of `G`.

-- TODO: this is a placeholder.  A geometric formalization requires defining
-- graph drawings as continuous maps from topological realizations of `G` into
-- `ℝ²`, together with a count of transverse crossing points.  The placeholder
-- returns an arbitrary natural number via `Classical.choice`. -/
noncomputable def crossingNumber (_ : SimpleGraph α) : ℕ :=
  Classical.choice (⟨0⟩ : Nonempty ℕ)

/-- **Zarankiewicz's conjecture** (1954) — **open**.

For the complete bipartite graph `K_{m,n}` (here modeled as the complete
bipartite graph on `Fin m ⊕ Fin n`):
  `cr(K_{m,n}) = ⌊m/2⌋ · ⌊(m−1)/2⌋ · ⌊n/2⌋ · ⌊(n−1)/2⌋`.

The right-hand side counts the crossings in the standard cylindrical drawing. -/
@[category research open, AMS 5]
theorem zarankiewicz_conjecture (m n : ℕ) :
    crossingNumber (completeBipartiteGraph (Fin m) (Fin n)) =
      (m / 2) * ((m - 1) / 2) * (n / 2) * ((n - 1) / 2) := by
  sorry

/-- **Crossing Lemma** (Ajtai–Chvátal–Newborn–Szemerédi / Leighton, 1982) — resolved.

For any simple graph `G` with `|E| ≥ 4 |V|`:
  `cr(G) ≥ |E|³ / (64 · |V|²)`.

We state the inequality in terms of `Fintype.card` and `G.edgeFinset.card`. -/
@[category research solved, AMS 5]
theorem crossing_lemma [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (h : 4 * Fintype.card α ≤ G.edgeFinset.card) :
    (G.edgeFinset.card : ℝ) ^ 3 / (64 * (Fintype.card α : ℝ) ^ 2) ≤
      crossingNumber G := by
  sorry

-- Sanity checks

/-- `crossingNumber` is a natural number (nonneg). -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) : 0 ≤ crossingNumber G := Nat.zero_le _

/-- `crossingNumber` of any graph on `Fin 3` is a natural number (sanity). -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ crossingNumber G := Nat.zero_le _

/-- `crossingNumber` cast to `ℝ` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 5)) : (0 : ℝ) ≤ (crossingNumber G : ℝ) :=
  Nat.cast_nonneg _

end WrittenOnTheWallII.GraphCrossingNumber
