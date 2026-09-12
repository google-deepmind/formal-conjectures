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

import FormalConjecturesUtil

/-!
# Erdős Problem 934

*References:*
- [erdosproblems.com/934](https://www.erdosproblems.com/934)
- [BBPP83] Bermond, J.-C. and Bond, J. and Paoli, M. and Peyrat, C., _Graphs and interconnection
  networks: diameter and vulnerability_. (1983), 1--30.
- [CCJK22] Cambie, Stijn and Cames van Batenburg, Wouter and de Joannis de Verclos, Rémi and
  Kang, Ross J., _Maximizing line subgraphs of diameter at most {$t$}_. SIAM J. Discrete Math.
  (2022), 939--950.
- [CGTT90] Chung, F. R. K. and Gyárfás, A. and Tuza, Z. and Trotter, W. T., _The maximum number
  of edges in {$2K_2$}-free graphs of bounded degree_. Discrete Math. (1990), 129--135.
- [Er88] Erdős, P, _Problems and results in combinatorial analysis and graph theory_. Discrete
  Math. (1988), 81-92.
-/

open Filter SimpleGraph

namespace Erdos934

/--
The length of a shortest path in `G` joining an endpoint of `e` to an endpoint of `f`.
This is `⊤` if the edges lie in different components. Edges that share a vertex have
distance `0`. Equivalently, this is one less than the distance in the line graph of `G`.
-/
noncomputable def pathLengthBetweenEdges {V : Type*} (G : SimpleGraph V) (e f : Sym2 V) : ℕ∞ :=
  ⨅ u : {x : V // x ∈ e}, ⨅ v : {y : V // y ∈ f}, G.edist u.1 v.1

/--
`G` contains two (distinct) edges whose shortest joining path has length at least `t`.
-/
def HasFarEdges {V : Type*} (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ e ∈ G.edgeSet, ∃ f ∈ G.edgeSet, e ≠ f ∧ t ≤ pathLengthBetweenEdges G e f

/--
$h_t(d)$ is the least $m$ such that every finite graph of maximum degree at most $d$ with at
least $m$ edges has two edges whose shortest joining path has length at least $t$.
-/
noncomputable def h (t d : ℕ) : ℕ :=
  open scoped Classical in
  sInf {m | ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    G.maxDegree ≤ d → m ≤ G.edgeFinset.card → HasFarEdges G t}

/--
Let $h_t(d)$ be minimal such that every graph $G$ with $h_t(d)$ edges and maximal degree $\leq d$ contains two edges whose shortest path between them has length $\geq t$.

Estimate $h_t(d)$.
-/
@[category research open, AMS 5]
theorem erdos_934 :
    ∀ t, (fun d ↦ (h t d : ℝ)) =Θ[atTop] ((answer(sorry) : ℕ → ℕ → ℝ) t) := by
  sorry

end Erdos934
