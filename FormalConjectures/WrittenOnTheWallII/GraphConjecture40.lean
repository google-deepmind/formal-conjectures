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

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α)

/--
WOWII [Conjecture 40](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a nontrivial connected graph `G` the size `f(G)` of a largest induced forest
satisfies `f(G) ≥ ceil((p(G) + b(G) + 1)/2)` where `p(G)` is the path cover
number and `b(G)` is the largest induced bipartite subgraph size.
-/
@[category research open, AMS 5]
theorem conjecture40 (h_conn : G.Connected) (h_nontrivial : 1 < Fintype.card α) :
    ⌈((p G + b G + 1) / 2)⌉ ≤ f G := by
  sorry

end SimpleGraph
