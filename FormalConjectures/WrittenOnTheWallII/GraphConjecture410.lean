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
# Written on the Wall II — Conjecture 410a and 410b

*References:*
- [E. DeLaVina, Written on the Wall II](https://cms.uhd.edu/faculty/delavinae/research/wowII/open.html)
- [J. J. Gebendorfer, A Regular-Graph Dichotomy for Maximum Critical Independent Sets, 31 August 2026](https://github.com/google-deepmind/formal-conjectures/issues/7268)

Distance zero is counted as even. The certificate also proves that excluding
it leaves both extremal vertex sets unchanged. The source already notes the
immediate nonregular case.
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture410

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

def minimumVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => ∀ w, G.degree v ≤ G.degree w
def maximumVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => ∀ w, G.degree w ≤ G.degree v
noncomputable def evenCount (G : SimpleGraph V) (v : V) : ℕ := by
  classical
  exact (univ.filter fun w => Even (G.dist v w)).card
noncomputable def evenMax (G : SimpleGraph V) : Finset V := by
  classical
  exact univ.filter fun v => ∀ w, evenCount G w ≤ evenCount G v
noncomputable def evenMin (G : SimpleGraph V) : Finset V := by
  classical
  exact univ.filter fun v => ∀ w, evenCount G v ≤ evenCount G w
def edgesOn (G : SimpleGraph V) [DecidableRel G.Adj] (Q : Finset V) : ℕ :=
  (G.edgeFinset.filter fun e => e.toFinset ⊆ Q).card
def baseBound (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (univ \ minimumVertices G).card + (univ \ maximumVertices G).card

/-- WOWII410a: bound the union of maximum-cardinality critical independent sets
using minimum- and maximum-degree complements and the edges on vertices maximizing
the number of vertices at even distance. -/
@[category research solved, AMS 5, formal_proof using lean4 at
"https://github.com/RhudeJJJJ/formal-conjectures/blob/86479d604b592946dc77246190b0f845517b6205/Proofs/WOWII410Proof.lean"]
theorem conjecture410a : ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → 2 < Fintype.card V →
    (criticalUnion G).card ≤ baseBound G + edgesOn G (evenMax G) := by
  sorry

/-- WOWII410b: bound the union of maximum-cardinality critical independent sets
using minimum- and maximum-degree complements and the edges on vertices minimizing
the number of vertices at even distance. -/
@[category research solved, AMS 5, formal_proof using lean4 at
"https://github.com/RhudeJJJJ/formal-conjectures/blob/86479d604b592946dc77246190b0f845517b6205/Proofs/WOWII410Proof.lean"]
theorem conjecture410b : ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → 2 < Fintype.card V →
    (criticalUnion G).card ≤ baseBound G + edgesOn G (evenMin G) := by
  sorry

end WrittenOnTheWallII.GraphConjecture410
