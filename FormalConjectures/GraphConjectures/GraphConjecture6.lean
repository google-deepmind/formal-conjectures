/-
Copyright (c) 2025 Henryk Michalewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henryk Michalewski
-/

import FormalConjectures.GraphConjectures.Imports
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Definitions
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Invariants

open Classical

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/--
WOWII Conjecture 6 (resolved):
For a connected graph `G` we have
`Ls(G) ≥ 1 + n(G) - m(G) - a(G)` where `a(G)` is defined via independent sets.
-/
theorem conjecture6 (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected) :
  Ls G ≥ 1 + n G - m G - a G := by sorry

end SimpleGraph
