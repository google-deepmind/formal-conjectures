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

import FormalConjecturesUtil

/-!
# Written on the Wall II - Conjecture 1

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture1

open SimpleGraph

/--
WOWII [Conjecture 1](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G` the maximum number of leaves of a spanning
tree satisfies `Ls(G) ≥ n(G) + 1 - 2·m(G)` where `n(G)` counts vertices and
`m(G)` is the size of a maximum matching.

A formal proof reduces to a spanning tree `T`. If `I` is the set of non-leaves
of `T`, Hall's theorem applied to a bipartition of `T` gives a matching `M`
with `|I| + 1 ≤ 2 * |M|`. Since `|V|` is the sum of the numbers of leaves and
non-leaves, and every matching and leaf count constructed in `T` is admissible
for the corresponding supremum in `G`, the stated inequality follows.
-/

@[category research solved, AMS 5,
  formal_proof using lean4 at
    "https://github.com/MiskinAleksandr23/WOWII-1/blob/eda16f6e96b313bd112351ae9859133b77d537c9/WOWII1/GraphConjecture1.lean"]
theorem conjecture1 {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected) :
    (Fintype.card α : ℝ) + 1 - 2 * matchingNumber G ≤ (Ls G : ℝ) := by
  sorry

end WrittenOnTheWallII.GraphConjecture1
