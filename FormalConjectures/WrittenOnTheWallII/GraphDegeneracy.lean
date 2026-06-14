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
# Graph Degeneracy and the Coloring Bound

*Reference:*
[L. Lick and A. White, k-degenerate graphs, Canad. J. Math. 22 (1970) 1082–1096](https://doi.org/10.4153/CJM-1970-125-1)

## Definition

A graph `G` is **k-degenerate** if every induced subgraph has a vertex of
degree at most `k`.  The **degeneracy** `d(G)` is the smallest such `k`.

Equivalently, `d(G) = max { minDegree(H) | H induced subgraph of G }`.

## Conjecture

A classical greedy argument (resolved) shows:
  `χ(G) ≤ d(G) + 1`.

The bound is tight: for the complete graph `Kₙ`, `d(Kₙ) = n − 1` and `χ(Kₙ) = n`.
-/

namespace WrittenOnTheWallII.GraphDegeneracy

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The **degeneracy** of `G`: the maximum, over all nonempty induced subgraphs `H`,
of the minimum degree of `H`.

We take the supremum over all nonempty vertex subsets `S : Finset α` of
`minDegree(G[S])`.  For the empty set we contribute 0 so the `sup` is over a
nonempty domain (`Finset.univ` includes `∅`). -/
noncomputable def degeneracy (G : SimpleGraph α) : ℕ :=
  Finset.univ.sup (fun S : Finset α =>
    if S.Nonempty then (G.induce (S : Set α)).minDegree else 0)

/-- **Degeneracy coloring bound** — resolved (greedy coloring).

For any simple graph `G`,
  `χ(G) ≤ degeneracy(G) + 1`.

Proof sketch: order vertices by the degeneracy ordering (repeatedly remove a
minimum-degree vertex); a greedy coloring then uses at most `d(G) + 1` colors
since each vertex has at most `d(G)` earlier neighbors. -/
@[category research solved, AMS 5]
theorem chromaticNumber_le_degeneracy_add_one (G : SimpleGraph α) [DecidableRel G.Adj] :
    G.chromaticNumber ≤ (degeneracy G + 1 : ℕ∞) := by
  sorry

/-- **Degeneracy lower bound from clique number** — resolved.

For any simple graph `G`, `degeneracy(G) ≥ G.cliqueNum − 1`, because the
complete subgraph `Kₖ` is an induced subgraph with `minDegree = k − 1`. -/
@[category research solved, AMS 5]
theorem degeneracy_ge_cliqueNum_sub_one (G : SimpleGraph α) [DecidableRel G.Adj] :
    G.cliqueNum - 1 ≤ degeneracy G := by
  sorry

-- Sanity checks

/-- `degeneracy` is a natural number (nonneg). -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) : 0 ≤ degeneracy G := Nat.zero_le _

/-- `degeneracy` of any graph on `Fin 3` is a natural number (sanity). -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ degeneracy G := Nat.zero_le _

/-- `degeneracy` cast to `ℝ` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 5)) : (0 : ℝ) ≤ (degeneracy G : ℝ) :=
  Nat.cast_nonneg _

end WrittenOnTheWallII.GraphDegeneracy
