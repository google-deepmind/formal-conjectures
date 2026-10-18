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

/-- Connected graphs of order greater than two have no isolated vertices.
This makes the original WOWII hypotheses an instance of the stronger theorem. -/
@[category API, AMS 5]
omit [DecidableEq V] in
theorem connected_has_neighbor (hG : G.Connected)
    (horder : 2 < Fintype.card V) (v : V) : ∃ w, G.Adj v w := by
  have hcard : 1 < Fintype.card V := by omega
  obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card hcard v
  obtain ⟨u, hu⟩ := (hG v w).nonempty_neighborSet_left hw.symm
  exact ⟨u, hu⟩

/-- The original connected formulation is a direct corollary of the
isolate-free strengthened theorem, with no independent proof gap. -/
@[category research solved, AMS 5]
theorem conjecture412d (hG : G.Connected) (hb : G.IsBipartite)
    (horder : 2 < Fintype.card V) :
    G.totalDominationNumber ≤ (criticalUnion G).card := by
  have hni : ∀ v, ∃ w, G.Adj v w := connected_has_neighbor G hG horder
  exact (conjecture412d_isolate_free G hb hni).2 ▸
    (conjecture412d_isolate_free G hb hni).1

end WrittenOnTheWallII.GraphConjecture412d
