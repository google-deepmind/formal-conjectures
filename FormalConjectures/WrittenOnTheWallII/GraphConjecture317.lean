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
# Written on the Wall II - Conjecture 317

*References:*
- [E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
- [J. J. Gebendorfer, Three Well-Total-Domination Conjectures from the Written on the Wall II
  List](https://doi.org/10.5281/zenodo.21650036), Theorem 4.5.
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture317

open SimpleGraph

/--
Let $G$ be a finite simple connected graph of order greater than one.
If the order of a largest induced tree is at least the number of edges
in the complement of $G$, then $G$ is well totally dominated.

This is WOWII Conjecture 317, dated 4 March 2007. Gebendorfer's Theorem 4.5
(28 July 2026) proves the stronger conclusion that every minimal total
dominating set has cardinality two.
-/
@[category research solved, AMS 5]
theorem conjecture317 {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    (h : (Gᶜ).edgeFinset.card ≤ G.largestInducedTreeSize) :
    IsWellTotallyDominated G := by
  sorry

end WrittenOnTheWallII.GraphConjecture317
