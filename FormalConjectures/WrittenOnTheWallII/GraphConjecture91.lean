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
# Written on the Wall II — Conjecture 91

*References:*
- [E. DeLaVina, Written on the Wall II, Conjecture 91, 10 April 2004](https://cms.uhd.edu/faculty/delavinae/research/wowII/open.html)
- [J. J. Gebendorfer, The Bipartite–Forest Gap Is Unbounded in Claw-Free Graphs, 25 July 2026; written line-graph family and intake](https://github.com/google-deepmind/formal-conjectures/issues/7261)

The catalogue already records another refutation, obtained by bridging $K_{3,3}$
to $K_8$. The cited line-graph family is not asserted to be the first refutation.
The archived O status is not a current worldwide-openness claim.
-/

@[expose] public section
namespace WrittenOnTheWallII.GraphConjecture91
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def bipartiteNumber (G : SimpleGraph V) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset V, A.card = k ∧ (G.induce (A : Set V)).IsBipartite}

noncomputable def forestNumber (G : SimpleGraph V) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset V, A.card = k ∧ (G.induce (A : Set V)).IsAcyclic}

/-- The average independence number of the graphs induced by open neighborhoods. -/
noncomputable def averageLocalIndependence (G : SimpleGraph V) : ℚ := by
  classical
  exact (∑ v : V, ((G.induce (G.neighborSet v)).indepNum : ℚ)) / Fintype.card V

/-- It is false that every connected finite simple graph satisfies
$b(G)\le1+f(G)\lceil\operatorname{avg}_v\alpha(G[N(v)])\rceil/2$.
Both induced-subgraph invariants maximize their vertex orders; the factor one
half is retained as rational division after the ceiling of the average. -/
@[category research solved, AMS 5]
theorem conjecture91 : ¬ ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.Connected →
    (bipartiteNumber G : ℚ) ≤ 1 + (forestNumber G : ℚ) *
      (⌈averageLocalIndependence G⌉₊ : ℚ) / 2 := by
  sorry

end WrittenOnTheWallII.GraphConjecture91
