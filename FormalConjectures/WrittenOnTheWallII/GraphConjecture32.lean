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
# Written on the Wall II - Conjecture 32

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture32

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
WOWII [Conjecture 32](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph $G$,
$\operatorname{path}(G) \ge \operatorname{dist}\_{\operatorname{avg}}(A) + 0.5 \cdot \operatorname{ecc}\_{\operatorname{avg}}(M)$,
where $\operatorname{path}(G)$ is the floor of the average distance of $G$, $A$ is the
set of minimum-degree vertices, $M$ is the set of maximum-degree vertices,
$\operatorname{dist}\_{\operatorname{avg}}(A)$ is the average distance from all vertices
to $A$, and $\operatorname{ecc}\_{\operatorname{avg}}(M)$ is the average eccentricity
of the vertices in $M$.

The conjecture is false, the authors present a counterexample: "The path on 5 vertices
is a counterexample, path = 5, distavg(A) = 4 and the average of eccentricity of maximum
degree vertices is 8/3."
-/
@[category research solved, AMS 5]
theorem conjecture32 : answer(False) ↔
    ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected),
      let A : Finset α := Finset.univ.filter (fun v => G.degree v = G.minDegree)
      let M : Finset α := Finset.univ.filter (fun v => G.degree v = G.maxDegree)
      let eccavg (S : Finset α) : ℝ := (∑ v ∈ S, (G.eccentricity v).toNat) / (S.card : ℝ)
      distavg G A + (1 / 2 : ℝ) * eccavg M ≤ (path G : ℝ) := by
  sorry

-- Sanity checks

/-- The `path G` invariant cast to ℝ is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ (path G : ℝ) := Nat.cast_nonneg _

/-- In `K₃`, the max degree is 2. -/
@[category test, AMS 5]
example : (⊤ : SimpleGraph (Fin 3)).maxDegree = 2 := by decide +native

end WrittenOnTheWallII.GraphConjecture32
