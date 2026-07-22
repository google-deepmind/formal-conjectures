/-
Copyright 2025 The Formal Conjectures Authors.

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

import FormalConjecturesUtil

/-!
# Written on the Wall II - Conjecture 194

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Counterexample

The conjecture is false. Take a clique on vertices `0, ..., 10`, four additional vertices
`11, ..., 14` adjacent to every clique vertex, and three leaves attached at `11`, `12`, and `14`.
This connected graph has independence number `4`, while the sum of the independence numbers of its
vertex neighbourhoods is `54`, so their average is `3`. Thus it satisfies the conjecture's
hypothesis with equality. However, its three leaves would all have to be endpoints of a Hamiltonian
path, which is impossible.
-/

namespace WrittenOnTheWallII.GraphConjecture194

open Classical SimpleGraph

/--
WOWII [Conjecture 194](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`, if `α(G) ≤ 1 + l_avg(G)`, then `G` has a Hamiltonian path.
Here `α(G) = G.indepNum` is the independence number, and
`l_avg(G) = averageIndepNeighbors G` is the average over all vertices of the independence number
of the neighbourhood.
A Hamiltonian path is a walk visiting every vertex exactly once. The answer is no, as witnessed by
the 18-vertex graph described above.
-/
@[category research solved, AMS 5, formal_proof using formal_conjectures at
"https://github.com/anagnorisis2peripeteia/formal-conjectures/blob/4bff865a14c2cd61fefbffbe9c49cbfc5a89ac45/FormalConjectures/WrittenOnTheWallII/GraphConjecture194.lean#L128-L140"]
theorem conjecture194 : answer(False) ↔
    ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) (_h : G.Connected),
      (G.indepNum : ℝ) ≤ 1 + averageIndepNeighbors G →
      ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  sorry

-- Sanity checks

/-- The average indep-neighbors invariant `l G` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ averageIndepNeighbors G := by
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro v _
    exact Nat.cast_nonneg _
  · exact Nat.cast_nonneg _

/-- The edgeless graph on 2 vertices has 2 vertices. -/
@[category test, AMS 5]
example : Fintype.card (Fin 2) = 2 := by decide

end WrittenOnTheWallII.GraphConjecture194
