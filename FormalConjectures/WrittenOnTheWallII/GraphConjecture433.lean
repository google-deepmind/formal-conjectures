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
# Written on the Wall II — Conjecture 433-M

*References:*
- [E. DeLaVina, Written on the Wall II](https://cms.uhd.edu/faculty/delavinae/research/wowII/open.html)
- [J. J. Gebendorfer, A counterexample to the independent domination bound in WOWII 433, 6 September 2026](https://github.com/google-deepmind/formal-conjectures/issues/7274)

The primary row declares pendants P but displays M, omits the comparison sign,
and occurs beneath a lower-bound heading. This file records the explicitly
reconstructed maximum-degree/upper-bound reading. It does not recover historical
intent. The linked certificate verifies a 52-vertex witness.
-/

@[expose] public section
namespace WrittenOnTheWallII.GraphConjecture433
open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
def maximumVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => ∀ w, G.degree w ≤ G.degree v

def neighbors (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  univ.filter fun v => ∃ u ∈ S, G.Adj v u

noncomputable def squareDegree (G : SimpleGraph V) (v : V) : ℕ := by
  classical
  exact G.graphSquare.degree v

noncomputable def reciprocalSum (G : SimpleGraph V) : ℚ :=
  ∑ v : V, 1 / (squareDegree G v : ℚ)

noncomputable def bound (G : SimpleGraph V) [DecidableRel G.Adj] : ℚ :=
  ((neighbors G (maximumVertices G)).card : ℚ) / 2 * ⌊2 * reciprocalSum G⌋₊

/-- The explicit upper reading 433-M asserts for every connected finite simple
graph of order greater than three that
$i(G)\le\tfrac12|N(M)|\lfloor2\sum_v1/d_{G^2}(v)\rfloor$.
Here $M$ is the full maximum-degree set, $N(M)$ is the union of open
neighborhoods, and the square joins distinct vertices at distance at most two.
The floor applies to twice the entire reciprocal-degree sum.
The rational comparison is equivalent to the real-valued inequality.
The linked witness has independent domination number $27$ and bound $25$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
"https://github.com/RhudeJJJJ/formal-conjectures/blob/cada5b7cde4a534e3191239afc57bbdc666dbf50/Proofs/WOWII433Proof.lean"]
theorem conjecture433_upper_M : ¬ ∀ (W : Type) [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj], G.Connected → 3 < Fintype.card W →
      (G.indepDominationNumber : ℚ) ≤ bound G := by
  sorry

end WrittenOnTheWallII.GraphConjecture433
