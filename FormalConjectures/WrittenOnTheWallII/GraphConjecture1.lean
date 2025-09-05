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

namespace WrittenOnTheWallII.GraphConjecture1

open SimpleGraph

/--
WOWII [Conjecture 1](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G` the maximum number of leaves of a spanning
tree satisfies `Ls(G) ≥ n(G) + 1 - 2·m(G)` where `n(G)` counts vertices and
`m(G)` is the size of a maximum matching.
-/

@[category research solved, AMS 5]
theorem conjecture1 {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected) :
    n G + 1 - 2 * m G ≤ Ls G := by
  sorry

end WrittenOnTheWallII.GraphConjecture1
