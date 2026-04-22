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
# Graph Bandwidth

*Reference:*
[J. A. Bondy and U. S. R. Murty, Graph Theory, Springer, 2008, Chapter 1]

[P. Z. Chinn, J. Chvátalová, A. K. Dewdney, N. E. Gibbs, The bandwidth problem for graphs
and matrices — a survey, J. Graph Theory 6 (1982) 223–254](https://doi.org/10.1002/jgt.3190060302)

## Definition

Given a bijection `f : V(G) → {0, …, n-1}` (a **linear arrangement**), the
**cost** of `f` is the maximum over all edges `{u, v}` of `|f(u) - f(v)|`.
The **bandwidth** `B(G)` is the minimum cost over all linear arrangements.

Formally, using `Fin (Fintype.card α)` for the label set:
  `B(G) = min_f max_{ {u,v} ∈ E(G) } |f(u) − f(v)|`.

## Conjecture

**Classical diameter lower bound** (Harper 1964 / Chvátalová 1975) — resolved:
  `B(G) ≥ ⌈(|V(G)| − 1) / diam(G)⌉`
for any connected graph `G` with at least 2 vertices.

Proof sketch: any linear arrangement `f` places the two endpoints of a
diametral path at distance at most `n − 1` on the line, while those endpoints
are connected by a path of length `diam(G)`, forcing some edge to stretch by
at least `(n − 1) / diam(G)`.
-/

namespace WrittenOnTheWallII.GraphBandwidth

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The **bandwidth** of `G` is the minimum, over all bijections
`f : α ≃ Fin (Fintype.card α)`, of the maximum edge label-difference.

`sInf` over a set of natural numbers returns 0 when the set is empty;
here the set is always nonempty because `Fin (Fintype.card α)` is in bijection
with `α` (via `Fintype.equivFin`), so the bandwidth is well-defined. -/
noncomputable def bandwidth (G : SimpleGraph α) : ℕ :=
  sInf {k | ∃ f : α ≃ Fin (Fintype.card α),
    ∀ u v : α, G.Adj u v → (Int.natAbs ((f u : ℤ) - (f v : ℤ))) ≤ k}

/-- **Diameter lower bound for bandwidth** — resolved.

For any connected graph `G` on `n ≥ 2` vertices,
  `bandwidth(G) ≥ ⌈(n − 1) / diam(G)⌉`.

We state the equivalent form: `bandwidth(G) * diam(G) ≥ n − 1`, where
`diam(G) = (maxEccentricity G).toNat`.

Proof sketch: fix any arrangement `f`. The two endpoints of a diametral
path `v₀, v_d` satisfy `|f(v₀) - f(v_d)| ≤ bandwidth(G) * d`, while
`|f(v₀) - f(v_d)| ≤ n − 1`.  Conversely, each step of the diametral path
contributes at most `bandwidth(G)` to the separation, so
`n − 1 ≤ bandwidth(G) * diam(G)`. -/
@[category research solved, AMS 5]
theorem bandwidth_mul_diam_ge_card_sub_one (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected) (hn : 2 ≤ Fintype.card α) :
    Fintype.card α - 1 ≤ bandwidth G * (maxEccentricity G).toNat := by
  sorry

/-- **Bandwidth is at least 1** for any connected graph on ≥ 2 vertices — resolved.

A connected graph on two or more vertices has at least one edge, so any
arrangement must place two adjacent vertices at distance ≥ 1. -/
@[category research solved, AMS 5]
theorem bandwidth_pos (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected) (hn : 2 ≤ Fintype.card α) :
    1 ≤ bandwidth G := by
  sorry

-- Sanity checks

/-- `bandwidth` is a natural number (nonneg). -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) : 0 ≤ bandwidth G := Nat.zero_le _

/-- `bandwidth` of any graph on `Fin 3` is a natural number (sanity). -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ bandwidth G := Nat.zero_le _

/-- `bandwidth` cast to `ℝ` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 5)) : (0 : ℝ) ≤ (bandwidth G : ℝ) :=
  Nat.cast_nonneg _

end WrittenOnTheWallII.GraphBandwidth
