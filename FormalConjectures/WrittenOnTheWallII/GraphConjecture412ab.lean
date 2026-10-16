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
# Written on the Wall II — Conjectures 412a and 412b

*References:*
- [E. DeLaVina, Written on the Wall II, June 2010](https://cms.uhd.edu/faculty/delavinae/research/wowII/open.html)
- [J. J. Gebendorfer, Pendant-Support Inequalities for Graph Coronas and Resolutions of WOWII 412a and 412b, 1 September 2026](https://github.com/user-attachments/files/33356703/Jonas_Gebendorfer_WOWII_412ab_submission_R1_2026-09-01.zip)

Neighborhoods are literal unions of open vertex neighborhoods and can intersect
the input set. The largest-component parameter counts vertices, with value zero
on the empty graph. Maximum critical means maximum cardinality among critical
independent sets, not inclusion maximality. The corona is the union of maximum
independent sets, not the graph corona product.
-/

@[expose] public section
namespace WrittenOnTheWallII.GraphConjecture412ab
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

def pendants [DecidableRel G.Adj] : Finset V := univ.filter fun v => G.degree v = 1

def degreeTwo [DecidableRel G.Adj] : Finset V := univ.filter fun v => G.degree v = 2

noncomputable def largestComponentOrder (A : Finset V) : ℕ :=
  sSup (Set.range fun c : (G.induce (A : Set V)).ConnectedComponent => Nat.card c.supp)

noncomputable def independentOn (A : Finset V) : ℕ := (G.induce (A : Set V)).indepNum

/-- The bipartite clause412a is
$|H|\ge c_L(G[S])+\alpha(G[V\setminus N(S)])$, where $S=N(P)$.
Here $c_L$ is the order of a largest component and $H$ is the maximum critical
independent-set union. The graph is connected, finite, bipartite and has order
greater than two.
-/
@[category research solved, AMS 5]
theorem conjecture412a [DecidableRel G.Adj] (hG : G.Connected)
    (hb : G.IsBipartite) (horder : 2 < Fintype.card V) :
    largestComponentOrder G (neighbors G (pendants G)) +
      independentOn G (univ \ neighbors G (neighbors G (pendants G))) ≤
        (criticalUnion G).card := by
  sorry

/-- The bipartite clause412b is
$|H|\ge c_L(G[S])+\alpha(G[A_2])$, with $S=N(P)$ and $A_2$ the degree-two
set, for connected finite bipartite graphs of order greater than two.
-/
@[category research solved, AMS 5]
theorem conjecture412b [DecidableRel G.Adj] (hG : G.Connected)
    (hb : G.IsBipartite) (horder : 2 < Fintype.card V) :
    largestComponentOrder G (neighbors G (pendants G)) + independentOn G (degreeTwo G) ≤
      (criticalUnion G).card := by
  sorry

/-- The corona version of412a holds for every connected finite simple graph
of order greater than two, without a bipartite hypothesis.
-/
@[category research solved, AMS 5]
theorem conjecture412a_corona [DecidableRel G.Adj] (hG : G.Connected)
    (horder : 2 < Fintype.card V) :
    largestComponentOrder G (neighbors G (pendants G)) +
      independentOn G (univ \ neighbors G (neighbors G (pendants G))) ≤ (corona G).card := by
  sorry

/-- The corona version of412b holds for every connected finite simple graph
of order greater than two, without a bipartite hypothesis.
-/
@[category research solved, AMS 5]
theorem conjecture412b_corona [DecidableRel G.Adj] (hG : G.Connected)
    (horder : 2 < Fintype.card V) :
    largestComponentOrder G (neighbors G (pendants G)) + independentOn G (degreeTwo G) ≤
      (corona G).card := by
  sorry

end WrittenOnTheWallII.GraphConjecture412ab
