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
# Written on the Wall II - Conjecture 396

*References:*
- [E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc,
  Conjecture 396, January 2010](https://cms.uhd.edu/faculty/delavinae/research/wowII/open.html)
- [J. J. Gebendorfer, Connected counterexamples to Written on the Wall II
  Conjecture 396, 13 October 2026](https://github.com/google-deepmind/formal-conjectures/issues/7308)

The linked Lean certificate verifies an explicit connected 39-vertex counterexample.
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture396

open SimpleGraph

/-- Every vertex outside the set has at least two neighbors in the set. -/
def IsTwoDominating {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) : Prop :=
  ∀ v ∉ D, 2 ≤ (D.filter fun w => G.Adj v w).card

/-- The minimum order of a 2-dominating set. -/
noncomputable def twoDominationNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {n | ∃ D : Finset V, IsTwoDominating G D ∧ D.card = n}

/-- The number of vertices of degree `j`. -/
def degreeFrequency {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (j : ℕ) : ℕ :=
  (Finset.univ.filter fun v => G.degree v = j).card

/-- The maximum frequency of a degree in the finite degree sequence. -/
def maximumFrequency {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (Finset.range (Fintype.card V + 1)).sup (degreeFrequency G)

/-- The distinct degrees attaining the maximum frequency. -/
def degreeModes {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset ℕ :=
  (Finset.range (Fintype.card V + 1)).filter fun j => degreeFrequency G j = maximumFrequency G

/-- Edges from degree-at-least-three vertices to degree-below-three vertices. -/
def boundaryCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((Finset.univ ×ˢ Finset.univ).filter fun p : V × V =>
    G.Adj p.1 p.2 ∧ 3 ≤ G.degree p.1 ∧ G.degree p.2 < 3).card

/-- The three terms on the right side of WOWII Conjecture 396. -/
def proposedBound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (degreeModes G).card + maximumFrequency G + boundaryCount G

/--
WOWII Conjecture 396 proposed that every connected finite simple graph of order
greater than two satisfies
$$\gamma_2(G)\le dd_{\mathrm{mode}}+|M|+|E(A_3,V\setminus A_3)|,$$
where $dd_{\mathrm{mode}}$ counts the distinct modal degrees, $M$ is the vertex
set of the smallest modal degree, and $A_3$ consists of vertices of degree at
least three. Every modal degree has the same frequency, so $|M|$ equals
`maximumFrequency G`. Gebendorfer's witness has two tied modes, 6 and 7,
and $\gamma_2=12>10$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
"https://github.com/RhudeJJJJ/formal-conjectures/blob/a95d2f088ec6384d1739aaa115b750ba61b874f8/Proofs/WOWII396Proof.lean"]
theorem conjecture396 : answer(False) ↔
    ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      G.Connected → 2 < Fintype.card V →
        twoDominationNumber G ≤ proposedBound G := by
  sorry

end WrittenOnTheWallII.GraphConjecture396
