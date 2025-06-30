import FormalConjectures.GraphConjectures.Imports
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Definitions
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Invariants

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α)

/--
WOWII Conjecture 58 (open):
For a connected graph `G`, the size `f(G)` of a largest induced forest satisfies
`f(G) ≥ ceil( b(G) / average l(v) )` where `b(G)` is the largest induced
bipartite subgraph and `l(v)` is the independence number of `G.neighborSet v`.
-/
-- The number of vertices of a largest induced forest of the graph.
-- WOWII conjecture: If G is a simple connected graph, then f(G) ≥ CEIL[ b(G)/average of l (v)]
theorem conjecture58 (hG : G.Connected) :
  (G.f : ℝ) ≥ Nat.ceil ((G.b : ℝ) / G.l_avg) := by sorry

end SimpleGraph
