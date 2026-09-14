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
# Written on the Wall II - Conjecture 58

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Counterexample

The conjecture is false. A counterexample is given by taking $K_{3,3}$
(with bipartition $\{0,1,2\}$, $\{3,4,5\}$) and $K_{73}$ (on vertices $\{6,\ldots,78\}$),
then adding edges between vertex $0$ and every vertex of $K_{73}$.

This graph $G$ has $n = 79$ vertices and satisfies:
- $b(G) \ge 7$: the set $\{0,1,2,3,4,5,6\}$ induces a bipartite subgraph
- $f(G) \le 6$: the largest induced forest has at most 6 vertices
- $l_{\mathrm{avg}}(G) = 92/79$
- $\lceil b(G) / l_{\mathrm{avg}}(G) \rceil \ge 7 > 6 \ge f(G)$
-/

namespace WrittenOnTheWallII.GraphConjecture58

open SimpleGraph Finset


/--
WOWII [Conjecture 58](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a connected graph `G`, the size `f(G)` of a largest induced forest satisfies
`f(G) ≥ ceil( b(G) / average l(v) )` where `b(G)` is the largest induced
bipartite subgraph and `l(v)` is the independence number of `G.neighborSet v`.

This conjecture is false. A counterexample is the graph described in the module docstring
above: a $K_{3,3}$ joined to a $K_{73}$ via vertex $0$, giving
$\lceil b/l_{\mathrm{avg}} \rceil \ge 7 > 6 \ge f(G)$.

The counterexample has been found by Moritz Firsching and Goran Žužić using an
experimental pipeline.
-/
@[category research solved, AMS 5, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/4bd72a06842a10e1b8d7bb0fd6b1ef5e6bd20210/FormalConjectures/WrittenOnTheWallII/GraphConjecture58.lean#L772"]
theorem conjecture58 : answer(False) ↔
    ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected),
      Nat.ceil (G.b / G.l_avg) ≤ G.largestInducedForestSize := by
  sorry

end WrittenOnTheWallII.GraphConjecture58
