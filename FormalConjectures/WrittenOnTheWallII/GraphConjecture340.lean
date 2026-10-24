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
# Written on the Wall II - Conjecture 340

*Reference:* E. DeLaviña, Written on the Wall II, entry 340 (February 18, 2009),
[archived source](https://web.archive.org/web/20260723211215/http://cms.uhd.edu/faculty/delavinae/research/wowII/open.html).
The linked definitions specify the smallest degree mode when there is a tie.

*Counterexample:* [J. J. Gebendorfer, Double brooms refute Graffiti.pc Conjecture 340
on total domination in trees (2026)](https://github.com/RhudeJJJJ/formal-conjectures/blob/c83bae78200bf3277ec9fe8e4a3f61d7ee37da82/Sources/WOWII340/wowii340.pdf).

Gebendorfer's double broom $D(5,5)$ refutes the inequality: its total domination
number is $8$, whereas the proposed upper bound is $2+1\cdot5=7$.
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture340

open SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The leaves together with all their neighbors: $N(L) \cup L$. -/
def leafSupportVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun v => G.degree v = 1 ∨ ∃ w, G.degree w = 1 ∧ G.Adj v w

/-- The number of components in the subgraph induced by $N(L) \cup L$. -/
noncomputable def leafSupportComponents (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Nat.card (G.induce (leafSupportVertices G : Set V)).ConnectedComponent

/-- The universal inequality in WOWII 340, dated February 18, 2009. -/
def conjecture340Statement : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj], T.IsTree → 2 < Fintype.card V →
      T.totalDominationNumber ≤ leafSupportComponents T +
        T.smallestDegreeMode * T.dominationNumber

/-- The proposed total-domination bound for all trees of order greater than two is false. -/
@[category research solved, AMS 5,
  formal_proof using lean4 at "https://github.com/RhudeJJJJ/formal-conjectures/blob/c83bae78200bf3277ec9fe8e4a3f61d7ee37da82/Proofs/WOWII340Proof.lean#L176"]
theorem conjecture340 : ¬ conjecture340Statement := by
  sorry

end WrittenOnTheWallII.GraphConjecture340
