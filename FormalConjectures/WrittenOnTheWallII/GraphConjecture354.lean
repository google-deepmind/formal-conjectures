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
# Written on the Wall II — Conjecture 354, closed-neighborhood variant

*References:*
- [E. DeLaVina, Written on the Wall II](https://cms.uhd.edu/faculty/delavinae/research/wowII/open.html)
- [J. J. Gebendorfer, Closed-Neighborhood Components, Open Packings, and Total Domination in Trees](https://github.com/user-attachments/files/33373810/Gebendorfer_WOWII_354_Intake_2026-10-13.zip)
- [Deposited manuscript](https://doi.org/10.5281/zenodo.21553771)

These are independently stated closed-neighborhood results. The primary row354
instead displays an open neighborhood and is refuted by a five-vertex tree.
No identification of the closed variant with historical intent is assumed.
-/

@[expose] public section
namespace WrittenOnTheWallII.GraphConjecture354
open SimpleGraph Finset

noncomputable def componentsOn {V : Type*} (G : SimpleGraph V) (S : Finset V) : ℕ :=
  Nat.card (G.induce (S : Set V)).ConnectedComponent

def degreeTwo {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Finset V := univ.filter fun v => G.degree v = 2

def neighbors {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (A : Finset V) : Finset V :=
  univ.filter fun v => ∃ a ∈ A, G.Adj v a

def closedNeighbors {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (A : Finset V) : Finset V := A ∪ neighbors G A

noncomputable def openPackingNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ := by
  classical
  exact (univ.powerset.filter fun P : Finset V =>
    (P : Set V).Pairwise fun u v => Disjoint (G.neighborSet u) (G.neighborSet v)).sup card

/-- Every nontrivial finite simple tree $T$ and every set $A$ of vertices of
 degree at least two satisfy $2c(T[N[A]])\le\rho^o(T)\le\gamma_t(T)$.
 An open packing has pairwise disjoint open neighborhoods; adjacent packed
 vertices are permitted. Components include isolates, and $N[A]$ is closed.
-/
@[category research solved, AMS 5]
theorem closed_neighborhood_bound {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree)
    (horder : 1 < Fintype.card V) (A : Finset V)
    (hA : ∀ v ∈ A, 2 ≤ T.degree v) :
    2 * componentsOn T (closedNeighbors T A) ≤ openPackingNumber T ∧
      openPackingNumber T ≤ T.totalDominationNumber := by
  sorry

/-- The degree-two specialization gives
$2c(T[N[D_2(T)]])\le\gamma_t(T)$ for every nontrivial finite simple tree.
-/
@[category research solved, AMS 5]
theorem degree_two_bound {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree)
    (horder : 1 < Fintype.card V) :
    2 * componentsOn T (closedNeighbors T (degreeTwo T)) ≤ T.totalDominationNumber := by
  sorry

/-- The explicit closed-neighborhood variant associated with354 asserts
$|C(T)|c(T[N[D_2(T)]])\le\gamma_t(T)$ for every finite simple tree of order
 greater than two, where $C(T)$ is its eccentricity/radius center.
-/
@[category research solved, AMS 5]
theorem conjecture354_closed {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree)
    (horder : 2 < Fintype.card V) :
    Nat.card T.center * componentsOn T (closedNeighbors T (degreeTwo T)) ≤
      T.totalDominationNumber := by
  sorry

end WrittenOnTheWallII.GraphConjecture354
