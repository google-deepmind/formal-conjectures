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
# Written on the Wall II - Conjecture 31

The WOWII page records this as **Chung's theorem**. This radius bound is proved
in Section 2 of P. Erdős, M. Saks, and V. T. Sós, *Maximum Induced Trees in
Graphs*, J. Combin. Theory Ser. B **41** (1986), 61–79; the authors credit
Fan Chung for the proof. We state it here as a theorem; the formal proof is left
as `sorry` pending a Lean port of the argument.

Here $\mathrm{path}(G)$ is the maximum number of vertices in an induced path,
and $\mathrm{rad}(G)$ is the graph radius.

*References:*
- [E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
- [P. Erdős, M. Saks, V. T. Sós, Maximum Induced Trees in Graphs](https://doi.org/10.1016/0095-8956(86)90028-6)
-/

namespace WrittenOnTheWallII.GraphConjecture31

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
WOWII [Conjecture 31](http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj31)
(Chung):

For every simple connected graph $G$,
$\mathrm{path}(G) \ge 2 \cdot \mathrm{rad}(G) - 1$,
where $\mathrm{path}(G)$ is the maximum number of vertices in an induced path
and $\mathrm{rad}(G)$ is the graph radius.
-/
@[category research solved, AMS 5]
theorem conjecture31 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ) := by
  sorry

-- Sanity checks

/-- The `path G` invariant cast to ℤ is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ (path G : ℤ) := Int.natCast_nonneg _

/-- The radius cast to ℤ is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ (G.radius.toNat : ℤ) := Int.natCast_nonneg _

end WrittenOnTheWallII.GraphConjecture31
