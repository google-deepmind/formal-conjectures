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

import FormalConjecturesUtil

/-!
# Written on the Wall II - Conjecture 438b

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

WOWII 438b asks whether

`alpha₂(G) ≤ alpha(G) + alpha(G[V \ H₂]) + |E(G[H₂])|`,

where `H₂` is the set of vertices of degree at most two. The conjecture is
true. In fact, the same inequality holds with an arbitrary vertex subset in
place of `H₂`.
-/

namespace WrittenOnTheWallII.GraphConjecture438b

open SimpleGraph Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Edges of `G` whose two endpoints lie in `S`. -/
def internalEdges (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Finset (Sym2 V) :=
  G.edgeFinset.filter fun e => e.toFinset ⊆ S

/-- A vertex set is 2-independent when its induced graph has maximum degree
at most one. -/
def IsTwoIndependent (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Prop :=
  ∀ v ∈ S, (S.filter fun w => G.Adj v w).card ≤ 1

/-- Maximum cardinality of an independent subset contained in `B`. -/
noncomputable def indepNumOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset V) : ℕ :=
  by
    classical
    exact (B.powerset.filter fun (A : Finset V) => G.IsIndepSet (A : Set V)).sup card

/-- Maximum cardinality of a 2-independent vertex set. -/
noncomputable def alphaTwo (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  by
    classical
    exact (Finset.univ.powerset.filter fun S => IsTwoIndependent G S).sup card

/-- The source's low-degree layer `H₂`. -/
def lowDegreeLayer (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun v => G.degree v ≤ 2

/--
WOWII 438b states that every connected graph of order greater than three
satisfies
`alpha₂(G) ≤ alpha(G) + alpha(G[V \ H₂]) + |E(G[H₂])|`.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
"https://github.com/Kuberwastaken/c5-k4/blob/e62f216625438bc099707e466d2825ab483717a4/lean/GraphConjecture438b.lean"]
theorem conjecture438b : answer(True) ↔
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], G.Connected → 3 < Fintype.card V →
      alphaTwo G ≤ G.indepNum +
        indepNumOn G (Finset.univ \ lowDegreeLayer G) +
        (internalEdges G (lowDegreeLayer G)).card := by
  sorry

end WrittenOnTheWallII.GraphConjecture438b
