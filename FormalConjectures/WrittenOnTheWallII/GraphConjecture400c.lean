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
# Written on the Wall II - Conjecture 400c

*References:*
- [E. DeLaViña, Written on the Wall II, Conjecture 400c](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json)
- [Written on the Wall II, Definitions 89, 90 and 114](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/definitions.json)
- [Counterexample with an independent Lean 4 verification](https://github.com/adamben04/open-conjectures/tree/main/results/graffiti-pc-382d-400c)

The 40-vertex counterexample has annihilation number $23$ and minimum disparity $9$.
Its 2-domination number is $8$, exceeding the proposed bound $7$.
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture400c

/-- Conjecture 400c claimed that every connected graph $G$ on more than two vertices satisfies
$\gamma_2(G) \le \lfloor 3 A(G) / \mathrm{disp}_{\min}(G) \rfloor$. Here $\gamma_2(G)$ is the
smallest size of a set $D$ such that every vertex outside $D$ has at least two neighbors in $D$.
The annihilation number $A(G)$ is the largest $k$ for which the $k$ smallest degrees sum to at most
the number of edges. The minimum disparity $\mathrm{disp}_{\min}(G)$ is the smallest number of
distinct degrees in $G$ among the open neighbors of any vertex. It is positive because $G$ is
connected and has more than one vertex. This claim is false. -/
@[category research solved, AMS 5, formal_proof using lean4 at "https://github.com/adamben04/open-conjectures/blob/5d8340d799176a7e90a77ace38ffc56d62529938/results/graffiti-pc-382d-400c/Graffiti2Dom.lean"]
theorem conjecture400c :
    ¬ ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.Connected → 2 < Fintype.card V →
        let γ₂ := sInf {n : ℕ | ∃ D : Finset V, D.card = n ∧
          ∀ v ∉ D, 2 ≤ (D.filter (G.Adj v)).card}
        let dispMin := sInf (Set.range fun v =>
          ((G.neighborFinset v).image fun u => G.degree u).card)
        γ₂ ≤ 3 * G.annihilationNumber / dispMin := by
  sorry

end WrittenOnTheWallII.GraphConjecture400c
