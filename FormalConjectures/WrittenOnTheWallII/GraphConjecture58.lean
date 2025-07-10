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
WOWII [Conjecture 58](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a connected graph `G`, the size `f(G)` of a largest induced forest satisfies
`f(G) ≥ ceil( b(G) / average l(v) )` where `b(G)` is the largest induced
bipartite subgraph and `l(v)` is the independence number of `G.neighborSet v`.
-/
@[category research open, AMS 5]
theorem conjecture58 (hG : G.Connected) :
    Nat.ceil (G.b / G.l_avg) ≤ G.f := by
  sorry

end SimpleGraph
