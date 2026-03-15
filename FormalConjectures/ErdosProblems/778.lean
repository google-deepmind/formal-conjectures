/-
Copyright 2026 The Formal Conjectures Authors.

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
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Erdős Problem 778

*Reference:* [erdosproblems.com/778](https://www.erdosproblems.com/778)

Alice and Bob play a game on the edges of $K_n$, alternating colouring edges
by red (Alice) and blue (Bob). Alice goes first, and wins if at the end
the largest red clique is larger than any of the blue cliques.

Malekshahian and Spiro [MaSp24] proved that for the first game, the set of $n$
for which Bob wins has density at least $3/4$.

[Gu83] Guy, R.K., _Unsolved Problems in Number Theory_, 1983.

[MaSp24] Malekshahian, A. and Spiro, S., _On a clique-building game of Erdős_. arXiv:2410.18304 (2024).
-/

open SimpleGraph

namespace Erdos778

/-- A game state in the edge-coloring game on $K_n$:
    tracks which edges are colored red (Alice) and blue (Bob). -/
structure GameState (n : ℕ) where
  red : Finset (Sym2 (Fin n))
  blue : Finset (Sym2 (Fin n))
deriving Inhabited

/-- A strategy for a player in the edge-coloring game:
    given the current game state, choose the next edge to color. -/
def Strategy (n : ℕ) := GameState n → Sym2 (Fin n)

/-- Play the standard edge-coloring game on $K_n$ (alternating, one edge each, Alice first)
    to completion. Returns the final game state with all edges colored. -/
opaque playStandardGame (n : ℕ) (alice bob : Strategy n) : GameState n

/-- Play the modified (1-vs-2) game on $K_n$ (Alice colors one edge, then Bob colors two,
    repeating) to completion. Returns the final game state with all edges colored. -/
opaque playModifiedGame (n : ℕ) (alice bob : Strategy n) : GameState n

/--
Erdős Problem 778, Part 1 [Gu83]:

Does Bob have a winning strategy in the standard edge-coloring game on $K_n$
(alternating, Alice first) for all $n \geq 3$? That is, can he ensure his largest
blue clique is at least as large as Alice's largest red clique?
-/
@[category research open, AMS 5 91]
theorem erdos_778 : answer(sorry) ↔
    ∀ n : ℕ, 3 ≤ n →
    ∃ bob : Strategy n,
      ∀ alice : Strategy n,
        let final := playStandardGame n alice bob
        cliqueNum (fromEdgeSet (final.blue : Set (Sym2 (Fin n)))) ≥
        cliqueNum (fromEdgeSet (final.red : Set (Sym2 (Fin n)))) := by
  sorry

/--
Erdős Problem 778, Part 2 [Gu83]:

In the modified game on $K_n$ where Alice colors one edge (red) and Bob colors two edges
(blue) per round, does Bob have a winning strategy for all $n > 3$? That is, can he ensure his
largest blue clique is strictly larger than Alice's largest red clique?
-/
@[category research open, AMS 5 91]
theorem erdos_778.variants.modified_game : answer(sorry) ↔
    ∀ n : ℕ, 3 < n →
    ∃ bob : Strategy n,
      ∀ alice : Strategy n,
        let final := playModifiedGame n alice bob
        cliqueNum (fromEdgeSet (final.blue : Set (Sym2 (Fin n)))) >
        cliqueNum (fromEdgeSet (final.red : Set (Sym2 (Fin n)))) := by
  sorry

/--
Erdős Problem 778, Variant 3 (max-degree game) [Gu83]:

In the standard edge-coloring game on $K_n$ (alternating, Alice first), Alice wins if the
maximum degree of the red subgraph exceeds the maximum degree of the blue subgraph. Does Bob
have a winning strategy for all sufficiently large $n$? Malekshahian and Spiro [MaSp24] proved
that the set of $n$ for which Bob wins has density at least $2/3$.
-/
@[category research open, AMS 5 91]
theorem erdos_778.variants.max_degree_game : answer(sorry) ↔
    ∀ n : ℕ, 3 ≤ n →
    ∃ bob : Strategy n,
      ∀ alice : Strategy n,
        let final := playStandardGame n alice bob
        (fromEdgeSet (final.blue : Set (Sym2 (Fin n)))).maxDegree ≥
        (fromEdgeSet (final.red : Set (Sym2 (Fin n)))).maxDegree := by
  sorry

end Erdos778
