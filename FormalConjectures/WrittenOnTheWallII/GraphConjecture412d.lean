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
# Written on the Wall II — Conjecture 412d

*References:*
- [E. DeLaVina, Written on the Wall II, Conjecture 412d, June 2010](https://cms.uhd.edu/faculty/delavinae/research/wowII/open.html)
- [J. J. Gebendorfer, Total domination and the union of maximum critical independent sets in bipartite graphs, revision 11 October 2026](https://github.com/user-attachments/files/33355645/wowii-412d-total-domination.pdf)

The written proof extends the original connected graph statement to all finite
bipartite graphs without isolated vertices. Critical differences use integer
subtraction. Maximum critical sets have greatest cardinality among difference
maximizers, including the empty set among candidates.
-/

@[expose] public section
namespace WrittenOnTheWallII.GraphConjecture412d
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

/-- For every connected finite bipartite graph of order greater than two,
the union $H$ of all maximum critical independent sets has
$|H|\ge\gamma_t(G)$. Total domination requires every selected vertex to have
a selected neighbor as well.
-/
@[category research solved, AMS 5]
theorem conjecture412d (hG : G.Connected) (hb : G.IsBipartite)
    (horder : 2 < Fintype.card V) :
    G.totalDominationNumber ≤ (criticalUnion G).card := by
  sorry

/-- The stronger written result holds without connectedness or an order
cutoff: in every finite bipartite graph without isolates,
$\gamma_t(G)\le|corona(G)|=|H|$. The bipartite identification of the two unions
is standard and is credited separately in the source.
-/
@[category research solved, AMS 5]
theorem conjecture412d_isolate_free (hb : G.IsBipartite)
    (hni : ∀ v, ∃ w, G.Adj v w) :
    G.totalDominationNumber ≤ (corona G).card ∧ corona G = criticalUnion G := by
  sorry

end WrittenOnTheWallII.GraphConjecture412d
