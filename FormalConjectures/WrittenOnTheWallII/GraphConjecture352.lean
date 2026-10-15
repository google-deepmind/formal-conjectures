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
# Written on the Wall II — Conjecture 352

*References:*
- [E. DeLaVina, Written on the Wall II](https://cms.uhd.edu/faculty/delavinae/research/wowII/open.html)
- [J. J. Gebendorfer, exact counterexample certificate, 30 August 2026](https://github.com/google-deepmind/formal-conjectures/issues/7264)
- [S. Dubey, earlier public worklog](https://gist.github.com/siddhantdubey/22f22a7a23db5174ee59e32eaa8724aa)

The linked certificate verifies an 18-vertex witness isomorphic to Dubey's
earlier public witness. No first-refutation or global-minimality claim is made.
The source explicitly uses the closed degree-two neighborhood.
-/

@[expose] public section
namespace WrittenOnTheWallII.GraphConjecture352
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
def closedDegreeTwo (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun v => G.degree v = 2 ∨ ∃ u, G.degree u = 2 ∧ G.Adj v u
def maxVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun v => ∀ w, G.degree w ≤ G.degree v
noncomputable def averageMaxEccentricity (G : SimpleGraph V) [DecidableRel G.Adj] : ℚ :=
  (∑ v ∈ maxVertices G, Finset.univ.sup (fun w => G.dist v w) : ℕ) /
    ((maxVertices G).card : ℚ)

/-- Every finite simple tree of order greater than two was conjectured to satisfy
$\gamma_t(T)\ge c(T[N[D_2]])+\lceil\operatorname{ecc}_{\mathrm{avg}}(M)/2\rceil$,
where $D_2$ is the set of degree-two vertices, $M$ the maximum-degree vertices,
and $c$ counts induced connected components. The neighborhood is closed and
eccentricities are measured in the ambient tree. The witness has a total
dominating set of size seven and a proposed lower bound at least eight.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
"https://github.com/RhudeJJJJ/formal-conjectures/blob/8949070c3c71b6c09c00f2fa43849a543b3399ab/Proofs/WOWII352Proof.lean"]
theorem conjecture352 : ¬ ∀ (W : Type) [Fintype W] [DecidableEq W]
      (G : SimpleGraph W) [DecidableRel G.Adj], G.IsTree → 2 < Fintype.card W →
      Nat.card (G.induce (closedDegreeTwo G : Set W)).ConnectedComponent +
        ⌈averageMaxEccentricity G / 2⌉₊ ≤ G.totalDominationNumber := by
  sorry

end WrittenOnTheWallII.GraphConjecture352
