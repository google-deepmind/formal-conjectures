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

/-!
# Written on the Wall II - Conjecture 327

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture327

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/--
WOWII [Conjecture 327](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

Let `G` be a simple connected graph. If `3 · γ(G) = γ_i(G)`, then `G` is well
totally dominated, where `γ(G)` is the domination number of `G` and `γ_i(G)` is
the independent domination number of `G`.

**Proof Sketch:**
The conjecture states that if $3\gamma(G) = i(G)$ for a connected graph $G$, then $G$ is well totally dominated.
However, this conjecture is **FALSE**.

**Counterexample:**
Consider a graph $G$ with 12 vertices: $u, v, a_0, a_1, a_2, a_3, a_4, b_0, b_1, b_2, b_3, b_4$.
The edges are:
- $(u, v)$
- $(u, a_i)$ for all $i \in \{0, 1, 2, 3, 4\}$
- $(v, b_i)$ for all $i \in \{0, 1, 2, 3, 4\}$
- $(a_0, b_3), (a_1, b_3), (a_2, b_0), (a_3, b_0), (a_4, b_3), (a_4, b_4)$

Properties of $G$:
1. **Connected**: Yes, path exists between any two vertices through $u$ and $v$.
2. **Domination Number $\gamma(G)$**: The set $\{u, v\}$ dominates all vertices. Since there is no universal vertex, $\gamma(G) = 2$.
3. **Independent Domination Number $i(G)$**: The minimum independent dominating set has size 6 (e.g., $\{u, b_0, b_1, b_2, b_3, b_4\}$). Thus $i(G) = 6$.
4. **Condition**: $3 \gamma(G) = 3 \times 2 = 6 = i(G)$. The condition holds.
5. **Well Totally Dominated**: A graph is well totally dominated if all minimal total dominating sets have the same size.
   - $\{u, v\}$ is a minimal total dominating set of size 2.
   - $\{v, b_0, b_3\}$ is a minimal total dominating set of size 3.
   Since $2 \neq 3$, $G$ is NOT well totally dominated.

The counterexample has been found by Moritz Firsching and Goran Žužić using an
experimental pipeline.
-/
@[category research solved, AMS 5, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/6e85aabe821e6ddf718d050a5bd8f19a48e4f2d9/FormalConjectures/WrittenOnTheWallII/GraphConjecture327.lean#L233"]
theorem conjecture327 : answer(False) ↔
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hG : G.Connected)
      (_h : 3 * G.dominationNumber = G.indepDominationNumber),
      IsWellTotallyDominated G := by
  sorry

-- Sanity checks

/-- In `K₂`, the max degree is 1 (each vertex has exactly one neighbor). -/
@[category test, AMS 5]
example : (⊤ : SimpleGraph (Fin 2)).maxDegree = 1 := by decide +native

/-- In the path graph `P₃`, vertex 1 has degree 2. -/
@[category test, AMS 5]
example : (SimpleGraph.fromEdgeSet {s(0,1), s(1,2)} : SimpleGraph (Fin 3)).degree 1 = 2 := by
  decide +native
end WrittenOnTheWallII.GraphConjecture327
