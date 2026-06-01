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

import FormalConjectures.Util.ProblemImports

/-!
# Written on the Wall II - Conjecture 133

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture133

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
WOWII [Conjecture 133](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/):

For a simple connected graph $G$,
$\operatorname{path}(G) \ge \operatorname{rad}(G) +
\lfloor \mathrm{avg}_v\, l(v) \rfloor^{cC_4(G)}$,
where $\operatorname{path}(G)$ is the floor of the average distance,
$\operatorname{rad}(G)$ is the radius (minimum eccentricity, as a natural number),
$\mathrm{avg}_v\, l(v) = l(G)$ is the average independence number of vertex
neighbourhoods, and $cC_4(G)$ is the number of induced $C_4$ subgraphs.

We read DeLaVina's bracket notation `[average of λ(v)]` in the source as the
floor (a standard Graffiti.pc convention), hence `⌊l G⌋` in Lean.
-/
@[category research open, AMS 5]
theorem conjecture133 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let rad := G.radius.toNat
    let cC4 := countInducedC4 G
    (rad : ℝ) + (⌊l G⌋ : ℝ) ^ cC4 ≤ (path G : ℝ) := by
  sorry

-- Sanity checks

/-- The `path G` invariant is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ (path G : ℝ) := Nat.cast_nonneg _

/-- `radius` toNat is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ G.radius.toNat := Nat.zero_le _

end WrittenOnTheWallII.GraphConjecture133
