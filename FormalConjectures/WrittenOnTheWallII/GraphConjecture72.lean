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

import FormalConjectures.Util.ProblemImports

/-!
# Written on the Wall II - Conjecture 72

**Verbatim statement (WOWII #72, status O):**
> If G is a simple connected graph, then tree(G) ≥ CEIL[average of ecc(v) + maximum of λ(v) /3]

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj72


*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture72

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- `largestInducedTreeSize G` is the number of vertices in a largest induced subtree of `G`.
A tree is a connected acyclic graph; an induced tree is an induced subgraph that is a tree. -/
noncomputable def largestInducedTreeSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, s.card = n ∧ (G.induce (s : Set α)).IsTree }

/-- The average eccentricity of `G`: the mean of `eccentricity G v` over all vertices. -/
noncomputable def averageEccentricity (G : SimpleGraph α) : ℝ :=
  (∑ v : α, (G.eccentricity v).toNat) / (Fintype.card α : ℝ)

/--
WOWII [Conjecture 72](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`,
`tree(G) ≥ ⌈(ecc_avg(G) + max_v l(v)) / 3⌉`
where `tree(G)` is the number of vertices in a largest induced tree,
`ecc_avg(G)` is the average eccentricity of `G`, and
`max_v l(v) = max_v indepNeighborsCard G v` is the maximum over all vertices of
the independence number of the neighbourhood.
-/
@[category research open, AMS 5]
theorem conjecture72 (G : SimpleGraph α) (h : G.Connected) :
    let maxL := (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp)
    ⌈(averageEccentricity G + (maxL : ℝ)) / 3⌉ ≤ (largestInducedTreeSize G : ℝ) := by
  sorry

-- Sanity checks

/-- The `largestInducedTreeSize` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ largestInducedTreeSize G := Nat.zero_le _

/-- The average eccentricity is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ averageEccentricity G := by
  unfold averageEccentricity
  positivity

end WrittenOnTheWallII.GraphConjecture72
