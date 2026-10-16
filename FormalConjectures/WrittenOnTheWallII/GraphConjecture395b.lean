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
# Written on the Wall II - Conjecture 395b

*References:*
- [E. DeLaVina, Written on the Wall II, entry 395b and definitions
  90/45/100/56/66](https://cms.uhd.edu/faculty/delavinae/research/wowII/open.html)
- [J. J. Gebendorfer, A fifteen-vertex counterexample to Written on the Wall II
  Conjecture 395b, 14 October 2026](https://github.com/user-attachments/files/33452211/Gebendorfer_New_Manuscripts_2026-10-14.zip)

The archived statement uses the smallest modal degree class and the induced
minimum degree after deleting ambient minimum-degree vertices. The remainder
is required nonempty, avoiding an undefined source quantity. The certificate
proves a connected fifteen-vertex counterexample with values six and five.
The archive's historical status is not a present curator confirmation.
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture395b

open SimpleGraph Finset

def IsTwoDominating {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) : Prop :=
  ∀ v ∉ D, 2 ≤ (D.filter fun w => G.Adj v w).card

noncomputable def twoDominationNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {n | ∃ D : Finset V, IsTwoDominating G D ∧ D.card = n}

def degreeFrequency {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (j : ℕ) : ℕ :=
  (Finset.univ.filter fun v => G.degree v = j).card

def maximumFrequency {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (Finset.range (Fintype.card V + 1)).sup (degreeFrequency G)

def degreeModes {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset ℕ :=
  (Finset.range (Fintype.card V + 1)).filter fun j => degreeFrequency G j = maximumFrequency G

def smallestMode {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  WithTop.untopD 0 (degreeModes G).min

def minimumVertices {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun v => G.degree v = G.minDegree

def remaining {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ \ minimumVertices G

def proposedBound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  degreeFrequency G (smallestMode G) +
    (G.induce (remaining G : Set V)).minDegree +
    (Finset.univ.filter fun v => G.degree v < 3).card

/--
WOWII 395b proposed the upper bound $\gamma_2(G)\leq |M|+\delta(G[V\setminus A])+|V\setminus A_3|$
for connected finite simple graphs of order greater than two. Here $M$ is the
smallest modal-degree class, $A$ is the original minimum-degree class, and
$A_3$ contains the vertices of ambient degree at least three. The deleted
graph is required nonempty. Selected vertices are exempt from 2-domination.
The linked certificate refutes this bound with $\gamma_2=6$ and right side five.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
"https://github.com/RhudeJJJJ/formal-conjectures/blob/66d81217cd33c8c37a3b1846289423ccff5c9ba4/Proofs/WOWII395bProof.lean"]
theorem conjecture395b : answer(False) ↔
    ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → 2 < Fintype.card V →
        (remaining G).Nonempty → twoDominationNumber G ≤ proposedBound G := by
  sorry

end WrittenOnTheWallII.GraphConjecture395b
