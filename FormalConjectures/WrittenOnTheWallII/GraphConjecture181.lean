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
# Written on the Wall II - Conjecture 181

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

The expression `deg_avg(B(G²))` is formalized by measuring degrees in `G²`,
the graph whose maximum-eccentricity vertices induce `B(G²)`.

The conjecture is false for the triangular graph `T(7) = L(K₇)`: it has at
most 16 leaves in a spanning tree, largest induced bipartite subgraph order 6,
and independence number 3. Its square is `K₂₁`, whose vertices all have
degree 20, so the claimed inequality would give `22 ≥ 23`.
-/

namespace WrittenOnTheWallII.GraphConjecture181

open SimpleGraph

/-- The average degree, in `G²`, of the maximum-eccentricity vertices of `G²`. -/
noncomputable def squarePeripheryAverage {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℝ := by
  classical
  let square := graphSquare G
  let periphery := Finset.univ.filter fun v => v ∈ maxEccentricityVertices square
  exact (∑ v ∈ periphery, ((square.neighborFinset v).card : ℝ)) / periphery.card

/--
WOWII Conjecture 181 asked whether every nontrivial finite connected simple
graph `G` satisfies

`Ls G + b G ≥ G.indepNum + deg_avg(B(G²))`.

The answer is no, witnessed by `T(7) = L(K₇)`.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at "https://github.com/Kuberwastaken/c5-k4/blob/3bfa33d7470055a9a11d9ffde29186245dc3a329/lean/GraphConjecture181.lean#L1-L381"]
theorem conjecture181 : answer(False) ↔
    ∀ (V : Type) [Fintype V] [DecidableEq V] [Nontrivial V]
      (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
        Ls G + b G ≥ G.indepNum + squarePeripheryAverage G := by
  sorry

end WrittenOnTheWallII.GraphConjecture181
