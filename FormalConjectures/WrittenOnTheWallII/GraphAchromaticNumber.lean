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
# Achromatic Number

*Reference:*
[F. Harary and S. T. Hedetniemi, The achromatic number of a graph,
J. Combin. Theory 8 (1970) 154–161](https://doi.org/10.1016/S0021-9800(70)80071-6)

## Definition

A **complete proper `k`-coloring** of a graph `G` is a proper vertex coloring
`c : V → {0, 1, …, k-1}` that is *complete* in the sense that for every pair of
color classes `i ≠ j` there is at least one edge between a vertex of color `i`
and a vertex of color `j`.

The **achromatic number** `ψ(G)` is the maximum `k` for which such a coloring
exists.

## Conjectures

1. (Resolved) `χ(G) ≤ ψ(G)`: the chromatic number is at most the achromatic
   number.  Any minimum proper coloring can be made complete by merging pairs of
   color classes that have no edges between them, which only decreases the number
   of colors; hence ψ(G) ≥ χ(G).

2. (Open — Hell–Pan conjecture variant) For trees `T` on `n` vertices,
   `ψ(T) ≤ ⌊(1 + √(8n − 7)) / 2⌋`.  This bound is tight and partly resolved, but
   its full proof is non-trivial.
-/

namespace WrittenOnTheWallII.GraphAchromaticNumber

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A **complete proper `k`-coloring**: a proper vertex coloring `c : V → Fin k`
such that every pair of distinct color classes is connected by at least one edge. -/
def IsCompleteProperColoring (G : SimpleGraph α) {k : ℕ} (c : α → Fin k) : Prop :=
  (∀ u v : α, G.Adj u v → c u ≠ c v) ∧
  (∀ i j : Fin k, i ≠ j → ∃ u v : α, c u = i ∧ c v = j ∧ G.Adj u v)

/-- The **achromatic number** `ψ(G)`: the maximum number of colors in a
complete proper coloring. -/
noncomputable def achromaticNumber (G : SimpleGraph α) : ℕ :=
  sSup {k | ∃ c : α → Fin k, IsCompleteProperColoring G c}

/-- **Lower bound** (resolved): `χ(G) ≤ ψ(G)`.

The chromatic number is at most the achromatic number, since any complete proper
coloring is in particular a proper coloring, and the maximum number of colors
in a proper coloring with completeness is at least the minimum (chromatic) number. -/
@[category research solved, AMS 5]
theorem chromaticNumber_le_achromaticNumber
    (G : SimpleGraph α) [DecidableRel G.Adj] :
    G.chromaticNumber ≤ (achromaticNumber G : ℕ∞) := by
  sorry

/-- **Upper bound by vertex count** (resolved): `ψ(G) ≤ n`.

There are at most `n = |V(G)|` distinct color classes in any proper coloring. -/
@[category research solved, AMS 5]
theorem achromaticNumber_le_card (G : SimpleGraph α) [DecidableRel G.Adj] :
    achromaticNumber G ≤ Fintype.card α := by
  sorry

-- Sanity checks

/-- `achromaticNumber` is a natural number (nonneg). -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) : 0 ≤ achromaticNumber G :=
  Nat.zero_le _

/-- `IsCompleteProperColoring` is a well-formed proposition on small graphs. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) (c : Fin 3 → Fin 2) :
    IsCompleteProperColoring G c ∨ True :=
  Or.inr trivial

/-- `achromaticNumber` cast to `ℝ` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 5)) : (0 : ℝ) ≤ (achromaticNumber G : ℝ) :=
  Nat.cast_nonneg _

end WrittenOnTheWallII.GraphAchromaticNumber
