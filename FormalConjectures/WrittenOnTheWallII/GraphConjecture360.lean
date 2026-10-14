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
# Written on the Wall II - Conjecture 360

*References:*
- [E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc,
  Conjecture 360, 18 February 2009](https://cms.uhd.edu/faculty/delavinae/research/wowII/open.html)
- [J. J. Gebendorfer, Center distance and total domination in trees:
  a counterexample to Graffiti.pc Conjecture 360, 13 October 2026](https://github.com/google-deepmind/formal-conjectures/issues/7305)

This records the explicitly transcribed half-average version. Older archived
HTML leaves the multiplier blank; the manuscript documents the source distinction.
The linked Lean certificate verifies the explicit 41-vertex tree.
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture360

open SimpleGraph

/-- Vertices minimizing the maximum ambient graph distance to any vertex. -/
noncomputable def centers {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Finset V := by
  classical
  exact Finset.univ.filter fun v => ∀ w,
    Finset.univ.sup (fun x => G.dist v x) ≤ Finset.univ.sup (fun x => G.dist w x)

/-- Average distance from metric centers over pairs with distinct endpoints. -/
noncomputable def positiveCenterAverage {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℚ :=
  (∑ u ∈ centers G, ∑ v : V, G.dist u v : ℕ) /
    (((centers G).card * (Fintype.card V - 1) : ℕ) : ℚ)

/-- Leaves and vertices adjacent to a leaf. -/
def leafSupportVertices {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Set V :=
  {v | G.degree v = 1 ∨ ∃ w, G.degree w = 1 ∧ G.Adj v w}

/--
The explicit half-average version of WOWII Conjecture 360 proposed that every
finite simple tree $T$ of order greater than two satisfies
$$\gamma_t(T)\ge c(T[S\cup L])+\tfrac12\operatorname{dist}_{\mathrm{avg}}(C,V),$$
where $L$ is the leaf set, $S$ the support set, $C$ the metric center,
and $c$ counts connected components. Distances are measured in $T$.
The average excludes zero self-distances, so its denominator is $|C|(|V|-1)$.
Gebendorfer's witness has at least four leaf/support components,
positive center average $321/80$, and a total dominating set of order six.
The rational comparison is equivalent to the printed real-valued inequality.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
"https://github.com/RhudeJJJJ/formal-conjectures/blob/a95d2f088ec6384d1739aaa115b750ba61b874f8/Proofs/WOWII360Proof.lean"]
theorem conjecture360 : answer(False) ↔
    ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsTree → 2 < Fintype.card V →
      (Nat.card (G.induce (leafSupportVertices G)).ConnectedComponent : ℚ) +
        positiveCenterAverage G / 2 ≤ G.totalDominationNumber := by
  sorry

end WrittenOnTheWallII.GraphConjecture360
