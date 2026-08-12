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
# Written on the Wall II - Conjecture 172

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

The conjecture is false for the graph `D₉`, formed from two triangles by
joining distinguished vertices with a path of nine edges. It has at most four
leaves in a spanning tree. Its peripheral vertices have degree two, while the
two maximum-degree vertices of its square are at distance seven in the
original graph, so the claimed inequality would give `4 ≥ 8`.
-/

namespace WrittenOnTheWallII.GraphConjecture172

open SimpleGraph

/-- The maximum original-graph degree among the peripheral vertices. -/
noncomputable def peripheryMaxDegree {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ := by
  classical
  exact (Finset.univ.filter fun v => v ∈ maxEccentricityVertices G).sup
    fun v => (G.neighborFinset v).card

/-- The maximum-degree vertices of `G²`, presented using finite graph distance. -/
def squareMaximumDegreeVertices {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Set V :=
  let squareDegree (v : V) :=
    (Finset.univ.filter fun w => v ≠ w ∧ computable_dist G v w ≤ 2).card
  {v | squareDegree v = Finset.univ.sup squareDegree}

/--
WOWII Conjecture 172 asked whether every nontrivial finite connected simple
graph `G` satisfies
`Ls G ≥ -1 + Δ(B(G)) + dist_min(G, M(G²))`.
The answer is no, witnessed by `D₉`.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at "https://github.com/Kuberwastaken/c5-k4/blob/a948106ad2d2a5d291b6b99575fe78bf373e7e02/lean/GraphConjecture172.lean#L1-L384"]
theorem conjecture172 : answer(False) ↔
    ∀ (V : Type) [Fintype V] [DecidableEq V] [Nontrivial V]
      (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
        Ls G ≥ (-1 : ℝ) + peripheryMaxDegree G +
          distMin G (squareMaximumDegreeVertices G) := by
  sorry

end WrittenOnTheWallII.GraphConjecture172
