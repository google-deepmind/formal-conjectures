/-
Copyright (c) 2025 Henryk Michalewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henryk Michalewski
-/

import FormalConjectures.GraphConjectures.Imports
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Definitions
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Invariants

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α)

/- f(G) is provided by `GraphConjectures.Definitions`. -/

/- b(G) is provided by `GraphConjectures.Definitions`. -/

/-!
# WOWII Conjecture 40 (open)

For a nontrivial connected graph `G` the size `f(G)` of a largest induced forest
satisfies `f(G) ≥ ceil((p(G) + b(G) + 1)/2)` where `p(G)` is the path cover
number and `b(G)` is the largest induced bipartite subgraph size.
-/
theorem conjecture40 (h_conn : G.Connected) (h_nontrivial : 1 < Fintype.card α) :
  f G ≥ ⌈((p G + b G + 1) / 2)⌉ := by sorry

end SimpleGraph

