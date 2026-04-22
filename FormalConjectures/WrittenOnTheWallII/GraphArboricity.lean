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
# Graph Arboricity and the Nash-Williams Formula

*Reference:*
[C. St. J. A. Nash-Williams, Decomposition of finite graphs into forests,
J. London Math. Soc. 39 (1964) 12](https://doi.org/10.1112/jlms/s1-39.1.12)

## Definition

The **arboricity** `a(G)` of a graph `G` is the minimum number of forests
needed to cover all edges of `G`.  Formally:
  `a(G) = min { k | ∃ F₁, …, Fₖ forests such that E(G) ⊆ E(F₁) ∪ ⋯ ∪ E(Fₖ) }`.

## Conjecture

The **Nash-Williams formula** (1964, resolved) states:
  `a(G) = max { ⌈|E(H)| / (|V(H)| − 1)⌉ | H induced subgraph, |V(H)| ≥ 2 }`.

We state the classical upper bound `a(G) ≤ ⌈Δ(G) / 2⌉ + 1`
(a consequence of the Nash-Williams formula that follows from the bound
`|E(H)| ≤ |V(H)| · Δ(G) / 2`), which is an open Graffiti.pc-style conjecture.
-/

namespace WrittenOnTheWallII.GraphArboricity

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The **arboricity** of `G` is the minimum number of forests whose edge-union
covers `G`.  Each forest is represented as a `SimpleGraph α` with `IsAcyclic`.
The value is `0` for the edgeless graph and `∞`-safe via `sInf`. -/
noncomputable def arboricity (G : SimpleGraph α) : ℕ :=
  sInf {k | ∃ F : Fin k → SimpleGraph α,
    (∀ i, (F i).IsAcyclic) ∧ G ≤ ⨆ i, F i}

/-- **Nash-Williams formula** (1964) — resolved.

For any simple graph `G`,
  `arboricity(G) = max { ⌈|E(H)| / (|V(H)| − 1)⌉ | H induced subgraph, |V(H)| ≥ 2 }`.

We state the equivalent upper-bound consequence:
`a(G) ≤ ⌈Δ(G) / 2⌉ + 1`,
which follows because for any induced subgraph `H` with `|V(H)| ≥ 2`,
  `|E(H)| ≤ |V(H)| · Δ(G) / 2`,
giving `⌈|E(H)| / (|V(H)| − 1)⌉ ≤ ⌈Δ(G) / 2⌉ + 1`. -/
@[category research solved, AMS 5]
theorem arboricity_le_maxDegree_div_two_add_one (G : SimpleGraph α) [DecidableRel G.Adj] :
    arboricity G ≤ G.maxDegree / 2 + 1 := by
  sorry

/-- **Nash-Williams formula** — resolved: the lower bound direction.

For any induced subgraph `H` on a set `S` of vertices with `|S| ≥ 2`,
  `arboricity(G) ≥ ⌈|E(H)| / (|S| − 1)⌉`. -/
@[category research solved, AMS 5]
theorem arboricity_ge_induced_subgraph_bound (G : SimpleGraph α) [DecidableRel G.Adj]
    (S : Finset α) (hS : 2 ≤ S.card) :
    (G.induce (S : Set α)).edgeFinset.card / (S.card - 1) ≤ arboricity G := by
  sorry

-- Sanity checks

/-- `arboricity` is a natural number (nonneg). -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) : 0 ≤ arboricity G := Nat.zero_le _

/-- `arboricity` of a graph on `Fin 3` is a natural number (sanity). -/
@[category test, AMS 5]
example : 0 ≤ arboricity (⊥ : SimpleGraph (Fin 3)) := Nat.zero_le _

/-- `arboricity` cast to `ℝ` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 5)) : (0 : ℝ) ≤ (arboricity G : ℝ) :=
  Nat.cast_nonneg _

end WrittenOnTheWallII.GraphArboricity
