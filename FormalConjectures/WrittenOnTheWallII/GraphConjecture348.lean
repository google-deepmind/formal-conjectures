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
# Written on the Wall II - Conjecture 348

A lower bound on total domination in terms of the open neighborhood of the
vertices of degree two, excluding the degree-two vertices themselves.

*References:*
- [E. DeLaVina, Written on the Wall II](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
- [J. J. Gebendorfer, A degree-two-neighborhood bound for total domination in trees]
  (https://github.com/RhudeJJJJ/formal-conjectures/blob/d8348148865175409dc83ac241ce342f43d395c3/Papers/20261021/wowii348.tex)
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture348

open SimpleGraph

/-- The vertices outside $D_2(T)$ with at least one neighbor in $D_2(T)$.
All degrees and neighborhoods are computed in the original graph. -/
def externalDegreeTwoNeighbors {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun v => G.degree v ≠ 2 ∧ ∃ w, G.Adj v w ∧ G.degree w = 2

/--
WOWII 348 asks whether every tree of order greater than two satisfies
$3\gamma_t(T)\geq2|N_T(D_2(T))\setminus D_2(T)|$.
Here $N_T$ denotes the open neighborhood and $D_2(T)$ the ambient degree-two vertices.
The external Lean proof establishes $3|D|\geq2|N_T(D_2(T))\setminus D_2(T)|+2$
for every total dominating set $D$.
-/
@[category research solved, question, AMS 5,
  formal_proof using lean4 at
    "https://github.com/RhudeJJJJ/formal-conjectures/blob/432062b98c51996c0d55eb3785ee1f4c3290e50d/Proofs/Potential348.lean#L417"]
theorem conjecture348 :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], G.IsTree → 2 < Fintype.card V →
        2 * (externalDegreeTwoNeighbors G).card ≤ 3 * G.totalDominationNumber := by
  sorry

end WrittenOnTheWallII.GraphConjecture348
