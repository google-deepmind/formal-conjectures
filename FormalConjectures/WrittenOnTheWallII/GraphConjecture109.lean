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

import FormalConjecturesUtil

/-!
# Written on the Wall II - Conjecture 109

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture109

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
WOWII [Conjecture 109](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph $G$, the independence number $\alpha(G)$ satisfies
$\alpha(G) \le \lfloor (\mathrm{residue}(G) + 2 \cdot b(G)) / 3 \rfloor$, where
$\mathrm{residue}(G)$ is the Havel-Hakimi residue and $b(G)$ is the size of a
largest induced bipartite subgraph.

See: Favaron, Mahéo, Saclé (1991) for the residue; DeLaVina's Graffiti.pc for the conjecture.
-/
@[category research open, AMS 5]
theorem conjecture109 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (G.indepNum : ℝ) ≤ ⌊((residue G : ℝ) + 2 * b G) / 3⌋ := by
  sorry

-- Sanity checks

/-- The invariant `b G` is nonneg (cast of a natural number). -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ b G := Nat.cast_nonneg _

/-- The residue of $K_2$ equals $1$: degree sequence is $[1, 1]$; one Havel-Hakimi
step gives $[0]$, leaving a single zero. -/
@[category test, AMS 5]
example : residue (⊤ : SimpleGraph (Fin 2)) = 1 := by
  unfold residue; decide +native

end WrittenOnTheWallII.GraphConjecture109
