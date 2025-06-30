import FormalConjectures.GraphConjectures.Imports
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Definitions
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Invariants

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α)

-- f(G) is provided by `GraphConjectures.Definitions`.

-- b(G) is provided by `GraphConjectures.Definitions`.

/--
WOWII Conjecture 40 (open):
For a nontrivial connected graph `G` the size `f(G)` of a largest induced forest
satisfies `f(G) ≥ ceil((p(G) + b(G) + 1)/2)` where `p(G)` is the path cover
number and `b(G)` is the largest induced bipartite subgraph size.
-/
-- Theorem: If G is a simple connected graph on more than one vertex,
-- then f(G) ≥ ⌈(p(G) + b(G) + 1) / 2⌉
theorem conjecture40 (h_conn : G.Connected) (h_nontrivial : 1 < Fintype.card α) :
  f G ≥ ⌈((p G + b G + 1) / 2)⌉ := by sorry

end SimpleGraph
