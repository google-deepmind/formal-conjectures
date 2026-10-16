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
# Written on the Wall II — Conjectures 404–407

*References:*
- [E. DeLaVina, Written on the Wall II, January 2010](https://cms.uhd.edu/faculty/delavinae/research/wowII/open.html)
- [J. J. Gebendorfer, The Corona of a Graph Is 2-Dominating, 31 August 2026, revision R2](https://github.com/user-attachments/files/33373103/Gebendorfer_WOWII_404_407_Intake_2026-10-13.zip)

Private external neighbors lie outside the input set and have exactly one
neighbor in it. Maximum critical means largest cardinality among independent
sets maximizing the integer difference. The maximum-critical/corona bridge
in Konig–Egervary graphs is established literature and is credited in the
source. Paths in a path cover are vertex-disjoint and may be trivial.
-/

@[expose] public section
namespace WrittenOnTheWallII.GraphConjecture404To407
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

noncomputable def neighbors (I : Finset V) : Finset V := by
  classical
  exact univ.filter fun v => ∃ u ∈ I, G.Adj u v

noncomputable def difference (I : Finset V) : ℤ :=
  (I.card : ℤ) - (neighbors G I).card

def IsCriticalIndependent (I : Finset V) : Prop :=
  G.IsIndepSet (I : Set V) ∧ ∀ J : Finset V, G.IsIndepSet (J : Set V) →
    difference G J ≤ difference G I

def IsMaximumCriticalIndependent (I : Finset V) : Prop :=
  IsCriticalIndependent G I ∧ ∀ J : Finset V, IsCriticalIndependent G J →
    J.card ≤ I.card

noncomputable def criticalUnion : Finset V := by
  classical
  exact univ.filter fun v => ∃ I : Finset V, IsMaximumCriticalIndependent G I ∧ v ∈ I

def IsMaximumIndependent (G : SimpleGraph V) (I : Finset V) : Prop :=
  G.IsIndepSet (I : Set V) ∧ ∀ J : Finset V, G.IsIndepSet (J : Set V) → J.card ≤ I.card

noncomputable def corona (G : SimpleGraph V) : Finset V := by
  classical
  exact univ.filter fun v => ∃ I : Finset V, IsMaximumIndependent G I ∧ v ∈ I

def leaves [DecidableRel G.Adj] : Finset V := univ.filter fun v => G.degree v = 1
noncomputable def supports [DecidableRel G.Adj] : Finset V := neighbors G (leaves G)

def privateExternalNeighborCount [DecidableRel G.Adj] (A : Finset V) : ℕ :=
  (univ.filter fun v => v ∉ A ∧ (G.neighborFinset v ∩ A).card = 1).card

/-- Every finite simple graph has a 2-dominating corona: every vertex outside
the union of its maximum independent sets has at least two neighbors in it.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at
    "https://github.com/RhudeJJJJ/formal-conjectures/blob/0d1f9d08f4fa49d8d319cfe429fa54b36a267724/Proofs/CoronaTwoDominatingProof.lean#L12"]
theorem corona_two_dominating [DecidableRel G.Adj] :
    ∀ v, v ∉ corona G → 2 ≤ (G.neighborFinset v ∩ corona G).card := by
  sorry

/-- In every finite Konig–Egervary graph, the maximum critical independent-set
union has no private external neighbors. The KE equation uses the existing
real-valued maximum-matching API.
-/
@[category research solved, AMS 5]
theorem critical_union_private_neighbors [DecidableRel G.Adj]
    (hKE : (G.indepNum : ℝ) + G.matchingNumber = Fintype.card V) :
    privateExternalNeighborCount G (criticalUnion G) = 0 := by
  sorry

/-- On finite simple trees of order greater than two,404 asserts
$peN(H)\le2(|S|-1)$, with $S$ the support set. Subtraction is in the integers.
-/
@[category research solved, AMS 5]
theorem conjecture404 [DecidableRel G.Adj] (hT : G.IsTree)
    (horder : 2 < Fintype.card V) :
    (privateExternalNeighborCount G (criticalUnion G) : ℤ) ≤
      2 * ((supports G).card - (1 : ℤ)) := by
  sorry

/-- On finite simple trees of order greater than two,405 asserts
$peN(H)\le2\alpha(T[V\setminus L])$, where $L$ is the leaf set.
-/
@[category research solved, AMS 5]
theorem conjecture405 [DecidableRel G.Adj] (hT : G.IsTree)
    (horder : 2 < Fintype.card V) :
    privateExternalNeighborCount G (criticalUnion G) ≤
      2 * (G.induce ((univ \ leaves G : Finset V) : Set V)).indepNum := by
  sorry

/-- On finite simple trees of order greater than two,406 asserts
$peN(H)\le peN(V\setminus L)-2$. Subtraction is in the integers.
-/
@[category research solved, AMS 5]
theorem conjecture406 [DecidableRel G.Adj] (hT : G.IsTree)
    (horder : 2 < Fintype.card V) :
    (privateExternalNeighborCount G (criticalUnion G) : ℤ) ≤
      (privateExternalNeighborCount G (univ \ leaves G) : ℤ) - 2 := by
  sorry

/-- On finite simple trees of order greater than two,407 asserts
$peN(H)\le2p(T)$, where $p(T)$ is the minimum number of vertex-disjoint
paths covering all vertices, as in the existing path-cover API.
-/
@[category research solved, AMS 5]
theorem conjecture407 [DecidableRel G.Adj] (hT : G.IsTree)
    (horder : 2 < Fintype.card V) :
    privateExternalNeighborCount G (criticalUnion G) ≤ 2 * G.pathCoverNumber := by
  sorry

end WrittenOnTheWallII.GraphConjecture404To407
