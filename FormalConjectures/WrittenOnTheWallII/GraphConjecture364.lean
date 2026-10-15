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
# Written on the Wall II — Conjecture 364

*References:*
- [E. DeLaVina, Written on the Wall II](https://cms.uhd.edu/faculty/delavinae/research/wowII/open.html)
- [J. J. Gebendorfer, On the Publicly Archived Formulation of Graffiti.pc Conjecture 364](https://github.com/google-deepmind/formal-conjectures/issues/7275)
- [S. Dubey, earlier public P4 counterexample](https://gist.github.com/siddhantdubey/22f22a7a23db5174ee59e32eaa8724aa)

This records the explicitly transcribed half-edge version. The factor applies
only to the edge term. Historical program output and curatorial intent are
not identified. The differently bracketed version is a separate statement.
-/

@[expose] public section
namespace WrittenOnTheWallII.GraphConjecture364
open SimpleGraph Finset

def supports {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => ∃ w, G.degree w = 1 ∧ G.Adj v w

def degreeTwo {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Finset V := univ.filter fun v => G.degree v = 2

def edgesOn {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  (G.edgeFinset.filter fun e => e.toFinset ⊆ S).card

def bound {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℚ :=
  ((supports G).card : ℚ) + (edgesOn G (degreeTwo G) : ℚ) / 2

/-- Every finite simple tree of order greater than two was conjectured to satisfy
$\gamma_t(T)\ge |S(T)|+\tfrac12|E(T[D_2(T)])|$, where $S$ consists of
vertices adjacent to leaves and $D_2$ consists of degree-two vertices.
The linked P4 certificate, following the earlier public Dubey witness,
has total domination number two and right-hand side $5/2$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
"https://github.com/RhudeJJJJ/formal-conjectures/blob/a4e07d0a5b53345446859e852daf80efa518e7c6/Proofs/WOWII364Proof.lean"]
theorem conjecture364 : ¬ ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.IsTree → 2 < Fintype.card V →
      bound G ≤ G.totalDominationNumber := by
  sorry

end WrittenOnTheWallII.GraphConjecture364
