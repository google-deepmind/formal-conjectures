/-
Copyright (c) 2025 Henryk Michalewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henryk Michalewski
-/

import FormalConjectures.GraphConjectures.Imports
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Definitions
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Invariants
 
open SimpleGraph

/--
WOWII Conjecture 1 (resolved):
For a simple connected graph `G` the maximum number of leaves of a spanning
tree satisfies `Ls(G) ≥ n(G) + 1 - 2·m(G)` where `n(G)` counts vertices and
`m(G)` is the size of a maximum matching.
-/

theorem conjecture1 {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected) :
    (Ls G) ≥ (n G) + 1 - 2 * (m G) := by
  sorry
