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
# Written on the Wall II — Conjecture 430c

*References:*
- [E. DeLaVina, Written on the Wall II](https://cms.uhd.edu/faculty/delavinae/research/wowII/open.html)
- [J. J. Gebendorfer, Two upper-bound readings of WOWII 430c, 7 September 2026](https://github.com/google-deepmind/formal-conjectures/issues/7273)

The primary row declares the center C but displays M, omits the comparison
sign and occurs beneath a lower-bound heading. This file records the explicitly
reconstructed upper/M and upper/center readings. It does not recover historical
intent. The parameter λ_max is maximum local independence, not spectral radius.
-/

@[expose] public section
namespace WrittenOnTheWallII.GraphConjecture430
open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
def maximumVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => ∀ w, G.degree w ≤ G.degree v
noncomputable def center (G : SimpleGraph V) : Finset V := by
  classical
  exact univ.filter fun v => G.eccent v = G.radius
noncomputable def squareResidue (G : SimpleGraph V) : ℕ := by
  classical
  exact G.graphSquare.residue
noncomputable def inducedMaxDegree (G : SimpleGraph V) (S : Finset V) : ℕ := by
  classical
  exact (G.induce (S : Set V)).maxDegree
noncomputable def boundOn (G : SimpleGraph V) (S : Finset V) : ℕ :=
  G.maxLocalIndependence * squareResidue G + inducedMaxDegree G S

/-- The explicit upper/M reading asserts that every connected finite simple
 graph of order greater than three satisfies
 $i(G)\le\lambda_{\max}(G)\,res(G^2)+\Delta(G[S])$,
 where $S$ is the full maximum-degree set. The local independence number at a
 vertex is the independence number of its induced open neighborhood.
 The graph square joins distinct vertices at distance at most two, and $res$
 is the Havel–Hakimi residue. The linked 105-vertex witness has independent
 domination number $65$ and a right-hand side at most $60$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
"https://github.com/RhudeJJJJ/formal-conjectures/blob/ea1662a77c26eb11be5b8634b7e8be9ca0992d85/Proofs/WOWII430Proof.lean"]
theorem conjecture430c_upper_M : ¬ ∀ (W : Type) [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj], G.Connected → 3 < Fintype.card W →
      G.indepDominationNumber ≤ boundOn G (maximumVertices G) := by
  sorry

/-- The explicit upper/center reading asserts that every connected finite simple
 graph of order greater than three satisfies
 $i(G)\le\lambda_{\max}(G)\,res(G^2)+\Delta(G[S])$,
 where $S$ is the full center. The local independence number at a
 vertex is the independence number of its induced open neighborhood.
 The graph square joins distinct vertices at distance at most two, and $res$
 is the Havel–Hakimi residue. The linked 105-vertex witness has independent
 domination number $65$ and a right-hand side at most $60$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
"https://github.com/RhudeJJJJ/formal-conjectures/blob/ea1662a77c26eb11be5b8634b7e8be9ca0992d85/Proofs/WOWII430Proof.lean"]
theorem conjecture430c_upper_center : ¬ ∀ (W : Type) [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj], G.Connected → 3 < Fintype.card W →
      G.indepDominationNumber ≤ boundOn G (center G) := by
  sorry

end WrittenOnTheWallII.GraphConjecture430
