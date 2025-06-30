import FormalConjectures.GraphConjectures.Imports
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Definitions
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Invariants

universe u

namespace SimpleGraph

variable {α : Type u} [Fintype α] [DecidableEq α]

/--
WOWII Conjecture 3 (resolved):
For a connected simple graph `G`, the number of leaves in a maximum spanning
tree satisfies `Ls(G) ≥ gi(G) * max_temp(G)`, where `gi(G)` is the independent
domination number and `max_temp(G)` is `max_v deg(v)/(n(G) - deg(v))`.
-/
-- If G is a simple connected graph, then Ls(G) ≥ gi(G) * max_temp(G)
theorem conjecture3 {G : SimpleGraph α} [DecidableEq α] [DecidableRel G.Adj] [Nonempty α] (h_conn : G.Connected) :
  (Ls G : ℝ) ≥ (gi G : ℝ) * (max_temp G) := by sorry

end SimpleGraph
