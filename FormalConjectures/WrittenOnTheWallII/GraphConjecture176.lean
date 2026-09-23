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
# Written on the Wall II - Conjecture 176

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

The conjecture is false for the graph `D₇`, formed from two triangles by
joining distinguished vertices with a path of seven edges. It has at most four
leaves in a spanning tree and largest induced bipartite subgraph order ten.
The two maximum-degree vertices of its square are at distance five in the
original graph, so the claimed inequality would give `14 ≥ 17`.
-/

namespace WrittenOnTheWallII.GraphConjecture176

open SimpleGraph

/-- The maximum-degree vertices of `G²`, presented using finite graph distance. -/
def squareMaximumDegreeVertices {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Set V :=
  let squareDegree (v : V) :=
    (Finset.univ.filter fun w => v ≠ w ∧ computable_dist G v w ≤ 2).card
  {v | squareDegree v = Finset.univ.sup squareDegree}

/--
WOWII Conjecture 176 asked whether every nontrivial finite connected simple
graph `G` satisfies
`Ls(G) + b(G) ≥ n(G) + dist_min(G, M(G²))`.
The answer is no, witnessed by `D₇`.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at "https://github.com/Kuberwastaken/c5-k4/blob/b0ba2b9206176b4fc30bd633de206ac230b4e01f/lean/GraphConjecture176.lean#L1-L377"]
theorem conjecture176 : answer(False) ↔
    ∀ (V : Type) [Fintype V] [DecidableEq V] [Nontrivial V]
      (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
        Ls G + b G ≥ (Fintype.card V : ℝ) +
          distMin G (squareMaximumDegreeVertices G) := by
  sorry

end WrittenOnTheWallII.GraphConjecture176
