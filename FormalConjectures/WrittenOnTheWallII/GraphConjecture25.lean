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

module

public import FormalConjecturesUtil

/-!
# Written on the Wall II - Conjecture 25

**Verbatim statement (WOWII #25, status F):**
> If G is a simple connected graph, then b(G) ≥ 2 CEIL[(1 + minimum of dist_even(v))/3]

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj25

The WOWII page records this conjecture as disproved (status F), with the same
counterexample as Conjecture 24.

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture25

open SimpleGraph

/--
WOWII [Conjecture 25](http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj25)
(status F, disproved):

For every finite simple connected graph $G$,
$b(G) ≥ 2⌈(1 + \min_v \operatorname{dist}_{\mathrm{even}}(v))/3⌉$,
where $b(G)$ is the size of a largest induced bipartite subgraph and
$\operatorname{dist}_{\mathrm{even}}(v)$ counts the vertices at even distance from $v$.

The nontrivial vertex type excludes graphs with fewer than two vertices.
The source gives the same counterexample as for Conjecture 24.
-/
@[category research solved, AMS 5]
theorem conjecture25 :
    ¬ ∀ {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α],
      ∀ (G : SimpleGraph α) (_ : G.Connected),
        let minDistEven := (Finset.univ.image (distEven G)).min' (by simp)
        2 * ⌈(1 + (minDistEven : ℝ)) / 3⌉ ≤ (b G : ℝ) := by
  sorry

-- Sanity checks

/-- The invariant `b G` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ b G := Nat.cast_nonneg _

/-- In $K_3$, only the vertex itself is at even distance. -/
@[category test, AMS 5]
theorem distEven_complete_three (v : Fin 3) : distEven (⊤ : SimpleGraph (Fin 3)) v = 1 := by
  simp [distEven, SimpleGraph.dist_top, apply_ite, Finset.filter_eq]

end WrittenOnTheWallII.GraphConjecture25
