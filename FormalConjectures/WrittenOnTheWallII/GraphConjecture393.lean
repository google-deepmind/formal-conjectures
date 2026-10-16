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
# Written on the Wall II — Conjectures 393a–c

*References:*
- [E. DeLaVina, Written on the Wall II, January 2010](https://cms.uhd.edu/faculty/delavinae/research/wowII/open.html)
- [J. J. Gebendorfer, Simultaneous sharpness of three pendant-neighborhood bounds for 2-domination](https://github.com/user-attachments/files/33373002/Gebendorfer_WOWII_393_Intake_2026-10-13.zip)

393a has an intact source formula. The set-operation glyphs in393b/c are lost;
we state their explicit intersection-normalized variants. The matching bound
is a specialization of DeLaVina–Larson–Pepper–Waller (2010), Theorem23, as
explained and credited in the linked manuscript. Neighborhoods are literal
unions of open vertex neighborhoods, not external neighborhoods.
-/

@[expose] public section
namespace WrittenOnTheWallII.GraphConjecture393
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

noncomputable def neighbors (I : Finset V) : Finset V := by
  classical
  exact univ.filter fun v => ∃ u ∈ I, G.Adj u v

def pendants [DecidableRel G.Adj] : Finset V := univ.filter fun v => G.degree v = 1
noncomputable def supports [DecidableRel G.Adj] : Finset V := neighbors G (pendants G)
noncomputable def remainder [DecidableRel G.Adj] : Finset V := univ \ neighbors G (supports G)

def IsTwoDominating [DecidableRel G.Adj] (D : Finset V) : Prop :=
  ∀ v, v ∉ D → 2 ≤ (G.neighborFinset v ∩ D).card

noncomputable def twoDominationNumber [DecidableRel G.Adj] : ℕ :=
  sInf {k | ∃ D : Finset V, IsTwoDominating G D ∧ D.card = k}

noncomputable def matchingNumberOn (A : Finset V) : ℝ := by
  classical
  exact (G.induce (A : Set V)).matchingNumber

def edgesOn [DecidableRel G.Adj] (A : Finset V) : ℕ :=
  (G.edgeFinset.filter fun e => e.toFinset ⊆ A).card

def uniqueNeighborCount [DecidableRel G.Adj] (A : Finset V) : ℕ :=
  (univ.filter fun v => (G.neighborFinset v ∩ A).card = 1).card

/-- With $P$ the leaves, $S=N(P)$, $R=N(S)$ and $U=V\setminus R$,
every connected finite simple graph of order greater than two satisfies
$\gamma_2(G)\le|U|+\mu(G[R])+|P|$. Two-domination constrains only vertices
outside the selected set. The matching parameter uses the existing real-valued
maximum-matching API, with no change in its integer mathematical value.
-/
@[category research solved, AMS 5]
theorem conjecture393a [DecidableRel G.Adj] (hG : G.Connected)
    (horder : 2 < Fintype.card V) :
    (twoDominationNumber G : ℝ) ≤ (remainder G).card +
      matchingNumberOn G (neighbors G (supports G)) + (pendants G).card := by
  sorry

/-- The explicit intersection variant393b is
$\gamma_2(G)\le|U|+|E(G[S])|+|\{v:|N(v)\cap S|=1\}|$
for connected finite simple graphs of order greater than two.
-/
@[category research solved, AMS 5]
theorem conjecture393b_intersection [DecidableRel G.Adj] (hG : G.Connected)
    (horder : 2 < Fintype.card V) :
    twoDominationNumber G ≤ (remainder G).card + edgesOn G (supports G) +
      uniqueNeighborCount G (supports G) := by
  sorry

/-- The explicit intersection variant393c is
$\gamma_2(G)\le|U|+|S|+|\{v:|N(v)\cap(P\cup S)|=1\}|$
for connected finite simple graphs of order greater than two.
-/
@[category research solved, AMS 5]
theorem conjecture393c_intersection [DecidableRel G.Adj] (hG : G.Connected)
    (horder : 2 < Fintype.card V) :
    twoDominationNumber G ≤ (remainder G).card + (supports G).card +
      uniqueNeighborCount G (pendants G ∪ supports G) := by
  sorry

end WrittenOnTheWallII.GraphConjecture393
