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
# Written on the Wall II — Conjecture 416

*References:*
- [E. DeLaVina, Written on the Wall II](https://cms.uhd.edu/faculty/delavinae/research/wowII/open.html)
- [J. J. Gebendorfer, A Universal-Vertex Reduction for Critical Independent Sets and WOWII Conjecture416, 31 August 2026](https://github.com/google-deepmind/formal-conjectures/issues/7270)

The compressed source expression `isolates(N(N(P)))` is interpreted on the
induced graph. The certificate proves the stronger bound without subtracting two.
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture416

open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def neighborhood (G : SimpleGraph V) (I : Finset V) : Finset V := by
  classical
  exact univ.filter fun v => ∃ u ∈ I, G.Adj u v

noncomputable def difference (G : SimpleGraph V) (I : Finset V) : ℤ :=
  (I.card : ℤ) - (neighborhood G I).card

def IsCritical (G : SimpleGraph V) (I : Finset V) : Prop :=
  G.IsIndepSet (I : Set V) ∧ ∀ J : Finset V,
    G.IsIndepSet (J : Set V) → difference G J ≤ difference G I

def IsMaximumCritical (G : SimpleGraph V) (I : Finset V) : Prop :=
  IsCritical G I ∧ ∀ J : Finset V, IsCritical G J → J.card ≤ I.card

noncomputable def criticalUnion (G : SimpleGraph V) : Finset V := by
  classical
  exact univ.filter fun v => ∃ I : Finset V, IsMaximumCritical G I ∧ v ∈ I

noncomputable def leaves (G : SimpleGraph V) : Finset V := by
  classical
  exact univ.filter fun v => G.degree v = 1

noncomputable def doubleNeighborhood (G : SimpleGraph V) : Finset V :=
  neighborhood G (neighborhood G (leaves G))

noncomputable def isolatesOn (G : SimpleGraph V) (Q : Finset V) : Finset V := by
  classical
  exact Q.filter fun v => ∀ w ∈ Q, ¬G.Adj v w

/-- WOWII416: for diameter at most two, the union of maximum-cardinality critical
independent sets bounds the isolates in the induced double neighborhood of the leaves,
up to the printed subtractive constant two. -/
@[category research solved, AMS 5, formal_proof using lean4 at
"https://github.com/RhudeJJJJ/formal-conjectures/blob/86479d604b592946dc77246190b0f845517b6205/Proofs/WOWII416Proof.lean"]
theorem conjecture416 : ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V), G.Connected → 2 < Fintype.card V →
    (∀ u v, G.dist u v ≤ 2) →
    ((isolatesOn G (doubleNeighborhood G)).card : ℤ) - 2 ≤ (criticalUnion G).card := by
  sorry

/-- The stronger bound removes the subtractive constant. -/
@[category research solved, AMS 5, formal_proof using lean4 at
"https://github.com/RhudeJJJJ/formal-conjectures/blob/86479d604b592946dc77246190b0f845517b6205/Proofs/WOWII416Proof.lean"]
theorem strengthened416 : ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V), G.Connected → 2 < Fintype.card V →
    (∀ u v, G.dist u v ≤ 2) →
    (isolatesOn G (doubleNeighborhood G)).card ≤ (criticalUnion G).card := by
  sorry

end WrittenOnTheWallII.GraphConjecture416
