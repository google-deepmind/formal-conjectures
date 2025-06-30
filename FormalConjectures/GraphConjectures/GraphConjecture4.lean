import FormalConjectures.GraphConjectures.Imports
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Definitions
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Invariants

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/--
WOWII Conjecture 4 (resolved):
If `G` is a connected graph then the maximum number of leaves over all spanning
trees satisfies `Ls(G) ≥ NG(G) - 1` where `NG(G)` is the minimal neighbourhood
size of a non-edge of `G`.
-/
theorem conjecture4 (G : SimpleGraph α) [DecidableRel G.Adj] [Nonempty α] (h_conn : G.Connected) :
  (Ls G : ℝ) ≥ NG G - 1 := by
  sorry

end SimpleGraph
