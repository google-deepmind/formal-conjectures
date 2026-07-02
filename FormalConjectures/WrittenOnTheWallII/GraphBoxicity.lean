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
# Graph Boxicity

*Reference:*
[F. S. Roberts, On the boxicity and cubicity of a graph, in Recent Progress in Combinatorics
(W. T. Tutte, ed.), Academic Press, 1969, pp. 301–310]

[A. Adiga, L. S. Chandran, N. Sivadasan, Lower bounds for boxicity,
Combinatorica 34 (2014) 631–655](https://doi.org/10.1007/s00439-013-1365-z)

[L. S. Chandran, M. C. Francis, N. Sivadasan, Boxicity and treewidth,
J. Combin. Theory Ser. B 97 (2007) 733–744](https://doi.org/10.1016/j.jctb.2006.12.004)

## Definition

The **boxicity** `box(G)` of a graph `G` is the minimum integer `d` such that
`G` is the intersection graph of a collection of axis-aligned boxes in `ℝᵈ`
(i.e., products of closed intervals).  Equivalently, `box(G)` is the minimum
number of interval graphs whose intersection (as edge sets) equals `G`.

A graph is an **interval graph** if it is the intersection graph of intervals
on the real line.  The boxicity is the minimum `d` such that `G` is the
intersection of `d` interval graphs on the same vertex set.

-- TODO: replace the `Classical.choice` placeholder with a proper definition
-- once Mathlib has formalised interval graph representations and intersection
-- graph constructions sufficiently for `sInf`-style minimisation.

## Conjecture

**Chandran–Francis–Sivadasan (2007)** — resolved:
  `box(G) ≤ tw(G) + 2`
where `tw(G)` is the treewidth of `G`.

This is an established upper bound; the proof uses tree decompositions to
construct an explicit box representation.

An open related conjecture is whether the bound can be improved to
`box(G) ≤ tw(G) + 1` in general.
-/

namespace WrittenOnTheWallII.GraphBoxicity

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The **boxicity** of `G`: the minimum dimension `d` such that `G` is the
intersection of `d` interval graphs on the vertex set `α`.

Equivalently, `box(G)` is the minimum `d` for which there exist interval
graphs `I₁, …, I_d` on `α` with `G = I₁ ⊓ ⋯ ⊓ I_d` (as `SimpleGraph α`).

-- TODO: this is a placeholder.  The proper definition requires:
-- (1) a notion of interval graphs on a `Fintype`,
-- (2) a proof that the empty graph has boxicity 0 and complete graphs have
--     boxicity 0 (they are trivially intersection graphs), and
-- (3) `sInf`-style minimisation over `d`. -/
noncomputable def boxicity (_ : SimpleGraph α) : ℕ :=
  Classical.choice (⟨0⟩ : Nonempty ℕ)

/-- The **treewidth** of `G`: the minimum width over all tree decompositions of `G`.

-- TODO: this is a placeholder.  Treewidth is not yet in Mathlib 4.27;
-- the proper definition uses tree decompositions (Finset-valued bags indexed
-- by a tree satisfying the standard bag-union and bag-connectivity conditions). -/
noncomputable def treewidth (_ : SimpleGraph α) : ℕ :=
  Classical.choice (⟨0⟩ : Nonempty ℕ)

/-- **Treewidth upper bound for boxicity** (Chandran–Francis–Sivadasan 2007) — resolved.

For any simple graph `G`,
  `box(G) ≤ tw(G) + 2`
where `tw(G)` is the treewidth of `G`.

Proof sketch: given a tree decomposition of width `tw(G)`, one constructs
`tw(G) + 2` interval graphs whose intersection equals `G` by processing
the bags of the decomposition. -/
@[category research solved, AMS 5]
theorem boxicity_le_treewidth_add_two (G : SimpleGraph α) [DecidableRel G.Adj] :
    boxicity G ≤ treewidth G + 2 := by
  sorry

/-- **Boxicity and maximum degree** (Roberts 1969 / Scheinerman 1984) — resolved.

For any simple graph `G` on `n` vertices,
  `box(G) ≤ ⌊n / 2⌋`.

This bound follows because every graph on `n` vertices can be represented
as the intersection of at most `n / 2` interval graphs. -/
@[category research solved, AMS 5]
theorem boxicity_le_card_div_two (G : SimpleGraph α) [DecidableRel G.Adj] :
    boxicity G ≤ Fintype.card α / 2 := by
  sorry

-- Sanity checks

/-- `boxicity` is a natural number (nonneg). -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) : 0 ≤ boxicity G := Nat.zero_le _

/-- `boxicity` of any graph on `Fin 3` is a natural number (sanity). -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ boxicity G := Nat.zero_le _

/-- `boxicity` cast to `ℝ` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 5)) : (0 : ℝ) ≤ (boxicity G : ℝ) :=
  Nat.cast_nonneg _

end WrittenOnTheWallII.GraphBoxicity
