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
# Written on the Wall II — Conjecture 365

*References:*
- [E. DeLaVina, Written on the Wall II, Conjecture 365, 18 February 2009](https://cms.uhd.edu/faculty/delavinae/research/wowII/open.html)
- [J. J. Gebendorfer, Isolated support vertices and degree-two edges in total domination of trees](https://github.com/user-attachments/files/33357101/Gebendorfer_365_Intake_2026-10-12.zip)

The manuscript proves the stronger integer inequality stated below. Its current
copy is undated. Isolates are taken inside the induced support graph, and the
second term counts induced edges with two degree-two endpoints.
-/

@[expose] public section
namespace WrittenOnTheWallII.GraphConjecture365
open SimpleGraph Finset

def supports {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => ∃ w, G.degree w = 1 ∧ G.Adj v w

def degreeTwo {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Finset V := univ.filter fun v => G.degree v = 2

def edgesOn {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  (G.edgeFinset.filter fun e => e.toFinset ⊆ S).card

def isolatedSupports {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Finset V :=
  (supports G).filter fun v => ∀ w ∈ supports G, ¬ G.Adj v w

/-- Every finite simple tree of order greater than two satisfies
$\gamma_t(T)\ge iso(T[S(T)])+|E(T[D_2(T)])|/3$.
Here $S(T)$ is the set of neighbors of leaves and $D_2(T)$ is the set of
vertices of degree two. The division is rational, with no downward rounding.
-/
@[category research solved, AMS 5]
theorem conjecture365 {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree)
    (horder : 2 < Fintype.card V) :
    ((isolatedSupports T).card : ℚ) + (edgesOn T (degreeTwo T) : ℚ) / 3 ≤
      T.totalDominationNumber := by
  sorry

/-- Gebendorfer's strengthening is
$\gamma_t(T)\ge iso(T[S(T)])+\lfloor |E(T[D_2(T)])|/3\rfloor+1$.
It improves the rounded original bound by one when the edge count is divisible
by three. The tree hypothesis and order restriction are retained.
-/
@[category research solved, AMS 5]
theorem conjecture365_strengthened {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree)
    (horder : 2 < Fintype.card V) :
    (isolatedSupports T).card + edgesOn T (degreeTwo T) / 3 + 1 ≤
      T.totalDominationNumber := by
  sorry

end WrittenOnTheWallII.GraphConjecture365
