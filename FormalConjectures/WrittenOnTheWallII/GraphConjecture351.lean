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
# Written on the Wall II — Conjecture 351

*References:*
- [E. DeLaVina, Written on the Wall II, Conjecture 351, 18 February 2009](https://cms.uhd.edu/faculty/delavinae/research/wowII/open.html)
- [J. J. Gebendorfer, An unbounded deficit in Graffiti.pc Conjecture 351](https://github.com/google-deepmind/formal-conjectures/issues/7236)

The source explicitly writes the second vertex set as $N(D_2)\cup D_2$.
It is a closed neighborhood. The undated manuscript gives a 44-vertex tree
with total domination number 20 and component-count sum 21, and a family
with unbounded deficit.
-/

@[expose] public section
namespace WrittenOnTheWallII.GraphConjecture351
open SimpleGraph Finset

def supports {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => ∃ w, G.degree w = 1 ∧ G.Adj v w

def leaves {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Finset V := univ.filter fun v => G.degree v = 1

noncomputable def componentsOn {V : Type*} (G : SimpleGraph V) (S : Finset V) : ℕ :=
  Nat.card (G.induce (S : Set V)).ConnectedComponent

def degreeTwo {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Finset V := univ.filter fun v => G.degree v = 2

def neighbors {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (A : Finset V) : Finset V :=
  univ.filter fun v => ∃ a ∈ A, G.Adj v a

def closedNeighbors {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (A : Finset V) : Finset V := A ∪ neighbors G A

/-- The original assertion that every finite simple tree of order greater than
 two satisfies $\gamma_t(T)\ge c(T[S(T)\cup L(T)])+c(T[N[D_2(T)]])$
 is false. Both terms count components of induced subgraphs, including isolates.
 The second neighborhood is closed, as explicitly printed in the source.
-/
@[category research solved, AMS 5]
theorem conjecture351 : ¬ ∀ (V : Type) [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj], T.IsTree → 2 < Fintype.card V →
      componentsOn T (supports T ∪ leaves T) +
        componentsOn T (closedNeighbors T (degreeTwo T)) ≤ T.totalDominationNumber := by
  sorry

end WrittenOnTheWallII.GraphConjecture351
