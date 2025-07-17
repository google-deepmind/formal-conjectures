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
WOWII [Conjecture 6](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a connected graph `G` we have
`Ls(G) ≥ 1 + n(G) - m(G) - a(G)` where `a(G)` is defined via independent sets.
-/
@[category research solved, AMS 5]
theorem conjecture6 (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected) :
    1 + n G - m G - a G ≤ Ls G := by
  sorry

end SimpleGraph
