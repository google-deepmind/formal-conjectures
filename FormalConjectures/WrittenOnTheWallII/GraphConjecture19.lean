/-
Copyright 2025 The Formal Conjectures Authors.

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

open Classical

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/--
WOWII [Conjecture 19](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

If `G` is connected then the size `b(G)` of a largest induced bipartite subgraph
satisfies
`b(G) ≥ FLOOR((∑ ecc(v))/(|V|) + sSup (range (l G)))`, where `ecc(v)` denotes
eccentricity and `l(G)` is the independence number of neighbourhoods.
-/
@[category research open, AMS 5]
theorem conjecture19 (G : SimpleGraph α) [Nonempty α] (h_conn : G.Connected) :
    FLOOR ((∑ v ∈ Finset.univ, ecc G v) / (Fintype.card α : ℝ) + sSup (Set.range (indepNeighbors G)))
      ≤ b G := by
  sorry

end SimpleGraph
