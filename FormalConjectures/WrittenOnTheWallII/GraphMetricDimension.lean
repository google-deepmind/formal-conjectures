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
# Metric Dimension of Graphs

*Reference:*
[G. Chartrand, L. Eroh, M. A. Johnson, O. R. Oellermann, Resolvability in graphs and the metric
dimension of a graph, Discrete Appl. Math. 105 (2000) 99–113](https://doi.org/10.1016/S0166-218X(00)00198-0)

## Definition

A set `R ⊆ V(G)` is a **resolving set** if for every two distinct vertices
`u, v`, there exists `r ∈ R` such that `dist(u, r) ≠ dist(v, r)`.

The **metric dimension** `dim(G)` is the minimum cardinality of a resolving set.

## Conjecture

A classical result (Chartrand et al., 2000, resolved) states:
  `dim(G) ≤ |V(G)| − diam(G)`
for any connected graph `G` with `|V(G)| ≥ 2`, where `diam(G)` is the diameter.

We also state the trivial resolved lower bound `dim(G) ≥ 1` for `|V(G)| ≥ 2`.
-/

namespace WrittenOnTheWallII.GraphMetricDimension

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- **Metric dimension lower bound** — resolved.

For any connected graph `G` with at least 2 vertices, `metricDimension(G) ≥ 1`.

Proof: any two distinct vertices `u, v` need to be distinguished, so the
resolving set must be nonempty. -/
@[category research solved, AMS 5]
theorem metricDimension_pos (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected) :
    1 ≤ metricDimension G := by
  sorry

/-- **Chartrand upper bound** (2000) — resolved.

For any connected graph `G` on `n ≥ 2` vertices,
  `metricDimension(G) ≤ n − diam(G)`
where `diam(G) = G.ediam.toNat`.

Proof sketch: a diametral path `v₀–v₁–⋯–v_d` of length `d = diam(G)` provides
a resolving set of size `n − d` by taking all vertices not on the path plus
suitable additional vertices; the bound follows from counting. -/
@[category research solved, AMS 5]
theorem metricDimension_le_card_sub_diam (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected) (hn : 2 ≤ Fintype.card α) :
    metricDimension G ≤ Fintype.card α - G.ediam.toNat := by
  sorry

-- Sanity checks

/-- `metricDimension` is a natural number (nonneg). -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) : 0 ≤ metricDimension G := Nat.zero_le _

/-- `IsResolvingSet` is a proposition that type-checks on `Fin 3`. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) (R : Finset (Fin 3)) : IsResolvingSet G R ∨ True :=
  Or.inr trivial

/-- `metricDimension` cast to `ℝ` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 5)) : (0 : ℝ) ≤ (metricDimension G : ℝ) :=
  Nat.cast_nonneg _

end WrittenOnTheWallII.GraphMetricDimension
