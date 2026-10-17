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
# Written on the Wall II — Conjecture 422d-U

*References:*
- [E. DeLaVina, Written on the Wall II](https://cms.uhd.edu/faculty/delavinae/research/wowII/open.html)
- [J. J. Gebendorfer, WOWII 422d: ein Gegenbeispiel auf zwölf Knoten und eine unbeschränkte Lücke, 7 September 2026](https://github.com/user-attachments/files/33373499/Gebendorfer_WOWII_422d_Intake_2026-10-13.zip)

The archived comparison glyph is missing and the containing heading says lower
bounds. This file records the explicitly reconstructed upper reading with
nonproper containment, including true twins. It does not claim to recover
historical intent. The proper-containment reading is a different statement.
-/

@[expose] public section
namespace WrittenOnTheWallII.GraphConjecture422
open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
def containingVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => ∃ u, u ≠ v ∧ ∀ w,
    (w = u ∨ G.Adj u w) → (w = v ∨ G.Adj v w)
def edgesOn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  (G.edgeFinset.filter fun e => e.toFinset ⊆ S).card
noncomputable def bound (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.induce ((univ \ containingVertices G : Finset V) : Set V)).indepNum +
    (edgesOn G (containingVertices G) + 1) / 3

/-- Under the explicitly reconstructed upper reading 422d-U, every connected
finite simple graph of order greater than three should satisfy
$i(G)\le\alpha(G[V\setminus D])+\lfloor(|E(G[D])|+1)/3\rfloor$,
where $D=\{v: \exists u\ne v, N[u]\subseteq N[v]\}$ uses nonproper
closed-neighborhood containment. The linked twelve-vertex witness has $i=4$
and right side $3$. The distinct proper-containment variant is not refuted.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
"https://github.com/RhudeJJJJ/formal-conjectures/blob/8949070c3c71b6c09c00f2fa43849a543b3399ab/Proofs/WOWII422dProof.lean"]
theorem conjecture422d_upper : ¬ ∀ (W : Type) [Fintype W] [DecidableEq W]
      (G : SimpleGraph W) [DecidableRel G.Adj], G.Connected → 3 < Fintype.card W →
      G.indepDominationNumber ≤ bound G := by
  sorry

end WrittenOnTheWallII.GraphConjecture422
