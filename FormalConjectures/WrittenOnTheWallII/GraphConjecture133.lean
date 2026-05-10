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
# Written on the Wall II - Conjecture 133

**Verbatim statement (WOWII #133, status O):**
> If G is a simple connected graph, then path(G) ≥ rad(G)+ [average of λ(v)]^^χC4

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj133


*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Definitions

`cC4 G` counts the number of **induced** 4-cycles in `G`.  We define this by
counting unordered 4-tuples `{a, b, c, d}` of distinct vertices (with a fixed
ordering to avoid overcounting) such that the induced subgraph on them is
isomorphic to the cycle `C₄`, i.e. the induced graph has exactly 4 edges
arranged as a 4-cycle.  Concretely, we check that the edge set of
`G.induce {a, b, c, d}` has exactly the 4 edges of some cyclic ordering.
-/

namespace WrittenOnTheWallII.GraphConjecture133

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- Check whether four distinct vertices form an induced 4-cycle in `G`.
We test all three perfect-matching pairings of the four vertices to find
a cyclic ordering and verify that the induced subgraph has exactly those 4 edges. -/
noncomputable def isInducedC4 (G : SimpleGraph α) [DecidableRel G.Adj]
    (a b c d : α) : Bool :=
  -- Cyclic orderings up to symmetry: (a-b-c-d), (a-b-d-c), (a-c-b-d)
  let check (p q r s : α) : Bool :=
    G.Adj p q && G.Adj q r && G.Adj r s && G.Adj s p &&
    !G.Adj p r && !G.Adj q s
  check a b c d || check a b d c || check a c b d

/-- Count of induced C₄ subgraphs of `G`. We count ordered 4-tuples `(a,b,c,d)`
of distinct vertices for which `isInducedC4 G a b c d = true`, then divide by
`24 = 4!`.

**Why 24 (and not 8)?** `isInducedC4` tests *all three* perfect-matching
pairings of the four vertices, so any of the `4! = 24` orderings of a fixed
unordered induced 4-cycle satisfies the predicate. Dividing by `8` (the size
of the dihedral group `D₄`) would overcount each induced 4-cycle by a factor
of `3` — once for each of the three cyclic structures `isInducedC4` accepts.
-/
noncomputable def countInducedC4 (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  (∑ a : α, ∑ b : α, ∑ c : α, ∑ d : α,
    if a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
       isInducedC4 G a b c d = true then 1 else 0) / 24

/--
WOWII [Conjecture 133](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`,
`path(G) ≥ rad(G) + ⌊avg_v l(v)⌋ ^ cC4(G)`
where `path(G)` is the floor of the average distance, `rad(G)` is the radius
(minimum eccentricity, as a natural number), `avg_v l(v) = l G` is the average
independence number of vertex neighbourhoods, and `cC4(G)` is the number of
induced C₄ subgraphs.
-/
@[category research open, AMS 5]
theorem conjecture133 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let rad := (minEccentricity G).toNat
    let cC4 := countInducedC4 G
    (rad : ℝ) + (⌊l G⌋ : ℝ) ^ cC4 ≤ (path G : ℝ) := by
  sorry

-- Sanity checks

/-- The `path G` invariant is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ (path G : ℝ) := Nat.cast_nonneg _

/-- `minEccentricity` toNat is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ (minEccentricity G).toNat := Nat.zero_le _

end WrittenOnTheWallII.GraphConjecture133
