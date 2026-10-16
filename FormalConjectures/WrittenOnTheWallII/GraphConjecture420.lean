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
# Written on the Wall II — Conjecture 420b and 420c

*References:*
- [E. DeLaVina, Written on the Wall II](https://cms.uhd.edu/faculty/delavinae/research/wowII/open.html)
- [J. J. Gebendorfer, A Common Counterexample Family for Two Graffiti.pc Bounds on Independent Domination, 1 September 2026](https://github.com/user-attachments/files/33356725/Jonas_J_Gebendorfer_WOWII_420b_420c_submission_package_R1_2026-09-01.zip)

The archived comparison glyphs are absent. The source note on triangle-free
420c determines the intended upper-bound direction. Both entries below use
that documented reconstruction and union-of-open-neighborhood convention.
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture420

open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def neighborhood (G : SimpleGraph V) [DecidableRel G.Adj] (I : Finset V) : Finset V :=
  univ.filter fun v => ∃ u ∈ I, G.Adj u v

def leaves (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => G.degree v = 1

def minVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => ∀ w, G.degree v ≤ G.degree w

def edgesOn (G : SimpleGraph V) [DecidableRel G.Adj] (I : Finset V) : ℕ :=
  (G.edgeFinset.filter fun e => e.toFinset ⊆ I).card

def residual (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ \ neighborhood G (neighborhood G (leaves G))

def closedMinimum (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  minVertices G ∪ neighborhood G (minVertices G)

noncomputable def sourceMinTriangles (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V := by
  classical
  exact univ.filter fun v => ∀ w, G.numTrianglesAtVertex v ≤ G.numTrianglesAtVertex w

noncomputable def bound420b (G : SimpleGraph V) [DecidableRel G.Adj] : ℤ :=
  (G.induce (residual G : Set V)).indepNum + 4 * ((edgesOn G (closedMinimum G) : ℤ) - 1)
noncomputable def bound420c (G : SimpleGraph V) [DecidableRel G.Adj] : ℤ :=
  (G.induce (residual G : Set V)).indepNum + 4 * (((sourceMinTriangles G).card : ℤ) - 1)

/-- WOWII420b, under the source-note-determined upper-bound reconstruction:
independent domination is bounded by the independence number outside the supports'
neighborhood plus four times one less than the edge count in the closed minimum-degree neighborhood. W8 refutes this. -/
@[category research solved, AMS 5, formal_proof using lean4 at
"https://github.com/RhudeJJJJ/formal-conjectures/blob/86479d604b592946dc77246190b0f845517b6205/Proofs/WOWII420Proof.lean"]
theorem conjecture420b : ¬ ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → 3 < Fintype.card V →
      (G.indepDominationNumber : ℤ) ≤ bound420b G := by
  sorry

/-- WOWII420c, under the source-note-determined upper-bound reconstruction:
independent domination is bounded by the independence number outside the supports'
neighborhood plus four times one less than the number of minimum-triangle vertices. W8 refutes this. -/
@[category research solved, AMS 5, formal_proof using lean4 at
"https://github.com/RhudeJJJJ/formal-conjectures/blob/86479d604b592946dc77246190b0f845517b6205/Proofs/WOWII420Proof.lean"]
theorem conjecture420c : ¬ ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → 3 < Fintype.card V →
      (G.indepDominationNumber : ℤ) ≤ bound420c G := by
  sorry

end WrittenOnTheWallII.GraphConjecture420
