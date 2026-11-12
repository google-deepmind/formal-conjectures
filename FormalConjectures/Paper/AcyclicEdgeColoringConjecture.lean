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
# The acyclic edge coloring conjecture

*References:*
* [Fi78] J. Fiamčík, *The acyclic chromatic class of a graph* (in Russian),
  Math. Slovaca 28 (1978), 139–145.
* [Bu79] M. I. Burnstein, *Every 4-valent graph has an acyclic 5-coloring* (in Russian),
  Soobšč. Akad. Nauk Gruzin. SSR 93 (1979), 21–24.
* [ASZ01] N. Alon, B. Sudakov, A. Zaks, *Acyclic edge colorings of graphs*,
  J. Graph Theory 37 (2001), 157–167. [doi:10.1002/jgt.1010](https://doi.org/10.1002/jgt.1010)
* Tao's optimization constant 55a:
  <https://teorth.github.io/optimizationproblems/constants/55a.html>,
  the asymptotic version $a'(G) \le C\Delta + o(\Delta)$, with known bounds.
-/

@[expose] public section

open SimpleGraph

namespace AcyclicEdgeColoringConjecture

/--
**The acyclic edge coloring conjecture (Fiamčík 1978 and Alon, Sudakov and Zaks 2001).**

Every finite simple graph $G$ with maximum degree $\Delta$ has an acyclic edge coloring with at most
$\Delta + 2$ colors, i.e. a proper edge coloring with no 2-colored cycle.

*Reference:* [ASZ01, Conjecture 1].
-/
@[category research open, AMS 5]
theorem acyclic_edge_coloring_conjecture :
    ∀ {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.AcyclicEdgeColourable (G.maxDegree + 2) := by
  sorry

/--
**The acyclic edge coloring conjecture holds for graphs with maximum degree at most 3.**

For maximum degree at most 2, the conjecture is trivial. For maximum degree 3, it follows from
[Bu79] applied to the line graph, as noted in [ASZ01].

*Reference:* [ASZ01, p. 159].
-/
@[category research solved, AMS 5]
theorem acyclic_edge_coloring_conjecture.variants.maxDegree_le_three :
    ∀ {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.maxDegree ≤ 3 →
      G.AcyclicEdgeColourable (G.maxDegree + 2) := by
  sorry

end AcyclicEdgeColoringConjecture
