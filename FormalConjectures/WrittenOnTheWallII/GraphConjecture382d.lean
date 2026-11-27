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
# Written on the Wall II - Conjecture 382d

*References:*
- [E. DeLaViña, Written on the Wall II, Conjecture 382d](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json)
- [Written on the Wall II, Definitions 4, 5, 14 and 90](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/definitions.json)
- [Counterexample with an independent Lean 4 verification](https://github.com/adamben04/open-conjectures/tree/main/results/graffiti-pc-382d-400c)

The 19-vertex counterexample has diameter $2$, independence number $4$, and exactly one vertex
of maximum local independence. Its 2-domination number is $6$, exceeding the proposed bound $5$.
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture382d

/-- Conjecture 382d claimed that every connected graph $G$ on more than two vertices satisfies
$\gamma_2(G) \le \operatorname{diam}(G)(\alpha(G)+|X|)/2$. Here $\alpha(G)$ is the independence
number and $X$ contains all vertices whose open neighborhoods have maximum independence number.
The 2-domination number $\gamma_2(G)$ is the smallest size of a set $D$ such that every vertex
outside $D$ has at least two neighbors in $D$. This claim is false. -/
@[category research solved, AMS 5, formal_proof using lean4 at "https://github.com/adamben04/open-conjectures/blob/main/results/graffiti-pc-382d-400c/Graffiti2Dom.lean"]
theorem conjecture382d :
    ¬ ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.Connected → 2 < Fintype.card V →
        let γ₂ := sInf {n : ℕ | ∃ D : Finset V, D.card = n ∧
          ∀ v ∉ D, 2 ≤ (D.filter (G.Adj v)).card}
        let X := Finset.univ.filter fun v => G.indepNeighborsCard v = G.maxLocalIndependence
        2 * γ₂ ≤ G.diam * (G.indepNum + X.card) := by
  sorry

end WrittenOnTheWallII.GraphConjecture382d
