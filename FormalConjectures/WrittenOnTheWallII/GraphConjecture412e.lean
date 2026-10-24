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
# Written on the Wall II — Conjecture 412e

*References:*
- [E. DeLaVina, Written on the Wall II, Conjecture 412e, June 2010](https://cms.uhd.edu/faculty/delavinae/research/wowII/open.html)
- [J. J. Gebendorfer, A neighborhood-exchange bound for maximum critical independent sets, 1 September 2026](https://github.com/user-attachments/files/33373335/Gebendorfer_WOWII_412e_Intake_2026-10-13.zip)

The source defines the neighborhood of a set as the union of vertex
neighborhoods. We state that literal convention first, then the stronger
external-neighborhood variant. A maximum critical independent set has maximum
cardinality among sets maximizing the critical difference.
-/

@[expose] public section
namespace WrittenOnTheWallII.GraphConjecture412e
open Finset SimpleGraph
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

noncomputable def externalNeighbors (A : Finset V) : Finset V := neighbors G A \ A

def pendants [DecidableRel G.Adj] : Finset V := univ.filter fun v => G.degree v = 1

noncomputable def inducedMaxDegree (A : Finset V) : ℕ := by
  classical
  exact (G.induce (A : Set V)).maxDegree

/-- For a connected finite bipartite graph of order greater than two, let $P$
be its pendant set and $H$ the union of all maximum critical independent sets.
Then $|H|\ge1+\Delta(G[N(N(P))])$ under the source's literal union of
neighborhoods. The induced empty graph has maximum degree zero.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at
    "https://github.com/RhudeJJJJ/formal-conjectures/blob/773d2ad877c643319608009a72a4c39eb71b5e86/Proofs/WOWII412FamilyProof.lean#L65"]
theorem conjecture412e [DecidableRel G.Adj] (hG : G.Connected)
    (hb : G.IsBipartite) (horder : 2 < Fintype.card V) :
    1 + inducedMaxDegree G (neighbors G (neighbors G (pendants G))) ≤
      (criticalUnion G).card := by
  sorry

/-- Under the external-neighborhood convention, the stronger bound is
$|H|\ge\alpha(G)\ge\Delta(G[N^\circ(N^\circ(P))])+\max\{2,|P|\}$.
Critical differences use integer subtraction; the two neighborhood conventions
agree on independent sets. The empty induced graph has maximum degree zero.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at
    "https://github.com/RhudeJJJJ/formal-conjectures/blob/773d2ad877c643319608009a72a4c39eb71b5e86/Proofs/WOWII412FamilyProof.lean#L73"]
theorem conjecture412e_external [DecidableRel G.Adj] (hG : G.Connected)
    (hb : G.IsBipartite) (horder : 2 < Fintype.card V) :
    inducedMaxDegree G (externalNeighbors G (externalNeighbors G (pendants G))) +
      max 2 (pendants G).card ≤ G.indepNum ∧ G.indepNum ≤ (criticalUnion G).card := by
  sorry

end WrittenOnTheWallII.GraphConjecture412e
