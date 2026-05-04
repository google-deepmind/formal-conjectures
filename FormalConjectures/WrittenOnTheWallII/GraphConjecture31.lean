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
# Written on the Wall II - Conjecture 31

**Verbatim statement (WOWII #31, status R):**
> If G is a simple connected graph, then path(G) ≥ 2 rad(G) - 1

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj31

The WOWII page records this as **Chung's theorem** (status R, "Reference"):
proved in F. R. K. Chung, *The average distance and the independence
number*, J. Graph Theory **12** (1988), 229-235. We state it here as a
theorem; the formal proof is left as `sorry` pending a Lean port of
Chung's argument.

Here `path(G)` is the floor of the average distance over ordered pairs
of distinct vertices (definition `path` in
`FormalConjecturesForMathlib`), and `rad(G)` is the graph radius.

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture31

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
WOWII [Conjecture 31](http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj31)
(status R, Chung 1988):

For every simple connected graph `G`,
`path(G) ≥ 2 rad(G) - 1`,
where `path(G)` is the floor of the average distance and `rad(G)` is the
graph radius.
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
