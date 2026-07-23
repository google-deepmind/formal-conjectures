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
# Written on the Wall II - Conjecture 7

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture7

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
WOWII [Conjecture 7](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph $G$,
$L_s(G) \ge \max_v \lambda(v) - 1 + n - 2 \alpha(G)$,
where $L_s(G)$ is the maximum number of leaves over all spanning trees of $G$,
$n = |V(G)|$, $\alpha(G) = G.\mathrm{indepNum}$ is the independence number, and
$\lambda(v) = \mathrm{indepNeighborsCard}\, G\, v$ is the independence number of the
neighbourhood of $v$.

Proved by DeLaVina, Fajtlowicz, Waller (2002).
-/
@[category research solved, AMS 5]
theorem conjecture7 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let maxL := (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp)
    ((maxL : ℤ) - 1 + (Fintype.card α : ℤ) - 2 * (G.indepNum : ℤ) : ℝ) ≤ Ls G := by
  sorry

-- Sanity checks

/-- The independence number is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ G.indepNum := Nat.zero_le _

end WrittenOnTheWallII.GraphConjecture7
