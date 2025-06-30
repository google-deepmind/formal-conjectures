import FormalConjectures.GraphConjectures.Imports
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Definitions
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Invariants

open BigOperators
open Classical

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/--
WOWII Conjecture 2 (open):
For a simple connected graph `G`,
`Ls(G) ≥ 2 · (l(G) - 1)` where `l(G)` is the average independence number of
the neighbourhoods of the vertices of `G`.

WOWII conjecture: If G is a simple   connected graph, then L s (G) ≥  2(average of l (v)   - 1)
-/
theorem conjecture2 (G : SimpleGraph α) (h : G.Connected) :
  Ls G ≥ 2 * (l G - 1) := by sorry

end SimpleGraph
