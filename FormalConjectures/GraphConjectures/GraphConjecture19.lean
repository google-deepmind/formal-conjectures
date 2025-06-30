import FormalConjectures.GraphConjectures.Imports
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Definitions
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Invariants

open BigOperators
open Classical

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/--
WOWII Conjecture 19 (open):
If `G` is connected then the size `b(G)` of a largest induced bipartite subgraph
satisfies
`b(G) ≥ FLOOR((∑ ecc(v))/(|V|) + sSup (range (l G)))`, where `ecc(v)` denotes
eccentricity and `l(G)` is the independence number of neighbourhoods.
-/
-- WOWII conjecture: If G is a simple     connected graph, then b(G) ≥ FLOOR(average of ecc(v)+maximum of l (v))
theorem conjecture19 (G : SimpleGraph α) [Nonempty α] (h_conn : G.Connected) :
    b G ≥ FLOOR ((∑ v ∈ Finset.univ, ecc G v) / (Fintype.card α : ℝ) + (sSup (Set.range (indepNeighbors G)))) := by sorry

end SimpleGraph
