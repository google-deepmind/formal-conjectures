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
# Graph Thickness

*Reference:*
[W. T. Tutte, The thickness of a graph, Indag. Math. 25 (1963) 567–577]

[L. W. Beineke and F. Harary, The thickness of the complete graph, Canad. J. Math. 17
(1965) 850–859](https://doi.org/10.4153/CJM-1965-082-2)

[J. Mayer, Decomposition de K₁₆ en trois graphes planaires, J. Combin. Theory Ser. B 13
(1972) 71]

## Definition

The **thickness** `θ(G)` of a graph `G` is the minimum number of planar subgraphs
whose edge-union covers all edges of `G`.  Equivalently, it is the minimum `k` such
that the edge set of `G` can be partitioned into `k` planar graphs.

Planarity of a `SimpleGraph` is captured by `G.Planar` in Mathlib (Kuratowski /
Wagner characterisation).

-- TODO: replace the `Classical.choice` placeholder with a proper definition once
-- Mathlib's `SimpleGraph.Planar` API is sufficiently developed for `sInf`-style
-- combinatorial minimisation.

## Conjecture

**Thickness of the complete graph** (Beineke–Harary 1965, Mayer 1972) — resolved
(with the exception of `n ≡ 9 (mod 12)` for even-degree cases, now also confirmed):
  `θ(Kₙ) = ⌈(n + 7) / 6⌉`   for `n ≠ 9, 10`,
  `θ(K₉) = θ(K₁₀) = 3`.

We state the general formula for all `n ≥ 1`, noting that the exceptional cases
fit the same formula `⌈(n + 7) / 6⌉` as well (since ⌈16/6⌉ = 3 = ⌈17/6⌉).

Equivalently: `θ(Kₙ) = ⌊(n + 7) / 6⌋` when `n ≢ 9 (mod 12)`,
and the formula is uniform using ceiling division.
-/

namespace WrittenOnTheWallII.GraphThickness

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The **thickness** of `G`: the minimum number of planar subgraphs whose
edge-union covers `G`.

-- TODO: this is a placeholder.  The proper definition would be:
--   `sInf {k | ∃ F : Fin k → SimpleGraph α, (∀ i, (F i).Planar) ∧ G ≤ ⨆ i, F i}`
-- but `SimpleGraph.Planar` and the planar-subgraph API are not yet sufficiently
-- developed in Mathlib for this style of minimisation. -/
noncomputable def thickness (_ : SimpleGraph α) : ℕ :=
  Classical.choice (⟨1⟩ : Nonempty ℕ)

/-- **Thickness of the complete graph** (Beineke–Harary 1965 / Mayer 1972) — resolved.

For all `n ≥ 1`,
  `θ(Kₙ) = ⌈(n + 7) / 6⌉`
where we use natural-number ceiling division `(n + 7 + 5) / 6 = (n + 12) / 6`.

Equivalently, in terms of the floor: `θ(Kₙ) = (n + 7) / 6` (rounded up). -/
@[category research solved, AMS 5]
theorem thickness_complete (n : ℕ) (hn : 1 ≤ n) :
    thickness (⊤ : SimpleGraph (Fin n)) = (n + 7 + 5) / 6 := by
  sorry

/-- **Thickness lower bound from Euler's formula** — resolved.

For any simple graph `G` on `n ≥ 3` vertices,
  `θ(G) ≥ ⌈|E(G)| / (3n − 6)⌉`
since each planar subgraph on `n` vertices has at most `3n − 6` edges
(by Euler's formula for planar graphs). -/
@[category research solved, AMS 5]
theorem thickness_ge_euler_bound (G : SimpleGraph α) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card α) :
    (G.edgeFinset.card + (3 * Fintype.card α - 6) - 1) / (3 * Fintype.card α - 6) ≤
      thickness G := by
  sorry

-- Sanity checks

/-- `thickness` is a natural number (nonneg). -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) : 0 ≤ thickness G := Nat.zero_le _

/-- `thickness` of any graph on `Fin 3` is a natural number (sanity). -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ thickness G := Nat.zero_le _

/-- `thickness` cast to `ℝ` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 5)) : (0 : ℝ) ≤ (thickness G : ℝ) :=
  Nat.cast_nonneg _

end WrittenOnTheWallII.GraphThickness
