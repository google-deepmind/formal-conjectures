/-
Copyright 2026 The Formal Conjectures Authors.

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
module

public import FormalConjecturesUtil

/-!
# Written on the Wall II - Conjecture 161

*References:*
- [E. DeLaViña, Written on the Wall II, Conjecture 161](http://cms.uhd.edu/faculty/delavinae/research/wowII/open.html)
- [D. B. West, Some Conjectures of Graffiti.pc, REGS 2009](https://dwest.web.illinois.edu/regs/graffiti.html)
- [J. J. Gebendorfer, Proper cliques and spanning-tree leaves (2026)](https://doi.org/10.13140/RG.2.2.31746.44485)
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture161

open SimpleGraph

/-- For every finite connected simple graph $G$, the maximum local independence number
of its complement is at most the maximum number of leaves in a spanning tree of $G$.
Leaves have degree one, so the one-vertex graph has leaf number zero. -/
@[category research solved, AMS 5]
theorem conjecture161 {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected) :
    (maxLocalIndependence Gᶜ : ℝ) ≤ Ls G := by
  sorry

end WrittenOnTheWallII.GraphConjecture161
