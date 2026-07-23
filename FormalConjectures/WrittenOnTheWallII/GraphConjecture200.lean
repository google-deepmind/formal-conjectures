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
# Written on the Wall II - Conjecture 200

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Counterexample

For every integer $q \geq 5$, let $C = \{a,b\} \cup D$ have $q$ vertices and
induce $K_q$ minus the edge $ab$. Add two nonadjacent vertices $x,y$, each
complete to $C$; a vertex $z$ adjacent exactly to $a,b$; and, for every
$d \in D$, a pendant vertex $p_d$ adjacent exactly to $d$.

The local-neighbourhood independence numbers are $2$ at $x,y,z$, $1$ at each
$p_d$, and $3$ at every vertex of $C$. Their sum is $4q+4$, while the graph has
$2q+1$ vertices, so
$$\left\lceil 1 + l_{\mathrm{avg}}(G)\right\rceil = 4.$$
The vertices $\{a,x,y,z\}$ induce a claw, and a case split on the number of
vertices from $C$ shows that no induced tree has more than four vertices.
Thus $\operatorname{tree}(G)=4$. Finally, the graph has $q-2 \geq 3$ pendant
vertices, but a Hamiltonian path has only two endpoints.

The smallest member of this family has 11 vertices and graph6 encoding
`J??FFBRq}N_`.
This is a smallest counterexample overall: an exhaustive search over all
11,989,760 connected graphs on 4 ≤ n ≤ 10 vertices (via nauty's `geng`;
graphs on at most 3 vertices are trivially traceable) found no graph
satisfying the premise without a Hamiltonian path.
-/

namespace WrittenOnTheWallII.GraphConjecture200

open Classical SimpleGraph

/--
WOWII [Conjecture 200](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`, if `tree(G) = ⌈1 + l_avg(G)⌉`, then `G` has a Hamiltonian path.
Here `tree(G)` is the number of vertices of a largest induced tree subgraph, and
`l_avg(G) = averageIndepNeighbors G` is the average over all vertices of the independence number
of the neighbourhood.
A Hamiltonian path is a walk visiting every vertex exactly once.

This conjecture is false. The counterexample family in the module docstring
satisfies the equality hypothesis and has no Hamiltonian path.
-/
@[category research solved, AMS 5, formal_proof using formal_conjectures at
  "https://github.com/infinityscroll/formal-conjectures/blob/9dd290db402c49922fa42793e4a7cfb802daf5c1/FormalConjectures/WrittenOnTheWallII/GraphConjecture200Counterexample.lean#L24-L195"]
theorem conjecture200 : answer(False) ↔
    ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) (_h : G.Connected),
      (largestInducedTreeSize G : ℝ) = ⌈1 + averageIndepNeighbors G⌉ →
      ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  sorry

-- Sanity checks

/-- The `largestInducedTreeSize` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ largestInducedTreeSize G := Nat.zero_le _

/-- The average indep-neighbors is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ averageIndepNeighbors G := by
  unfold averageIndepNeighbors
  apply div_nonneg
  · apply Finset.sum_nonneg; intro v _; exact Nat.cast_nonneg _
  · exact Nat.cast_nonneg _

end WrittenOnTheWallII.GraphConjecture200
