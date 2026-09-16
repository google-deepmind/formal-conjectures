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
# Written on the Wall II - Conjecture 34

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture34

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
WOWII [Conjecture 34](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph $G$,
$\operatorname{path}(G) \ge \lceil \operatorname{dist}\_{\operatorname{avg}}(C, V)
+ \operatorname{dist}\_{\operatorname{avg}}(M, V) \rceil$,
where $\operatorname{path}(G)$ is the number of vertices of a largest induced path of $G$,
$C$ is the set of center vertices (those with minimum eccentricity), $M$ is the set of
maximum-degree vertices, and $\operatorname{dist}\_{\operatorname{avg}}(S, V)$ is the average
of all nonzero distances $\operatorname{dist}\_G(s, v)$ with $s \in S$ and $v \in V$.

The conjecture is false. Let $G$ be the tree on $39$ vertices formed by a vertex with three
pendant leaves, joined by a path of five edges to the root of a perfect binary tree of depth
four. Then $\operatorname{path}(G) = 11$, while $C$ and $M$ are singletons whose distance sums
are $154$ and $266$, so the bound is $\lceil (154 + 266) / 38 \rceil = 12$.
-/
@[category research solved, AMS 5]
theorem conjecture34 :
  answer(False) ↔
    ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected),
      let C : Set α := center G
      let M : Set α := {v | G.degree v = G.maxDegree}
      let distAvg (S : Set α) : ℝ :=
        open scoped Classical in
        let pairs := (S.toFinset ×ˢ Finset.univ).filter (fun p => G.dist p.1 p.2 ≠ 0)
        (∑ p ∈ pairs, (G.dist p.1 p.2 : ℝ)) / pairs.card
      Int.ceil (distAvg C + distAvg M) ≤ (path G : ℤ) := by
  sorry

-- Sanity checks

/-- The `path G` invariant is nonneg when cast to ℤ. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ (path G : ℤ) := Int.natCast_nonneg _

/-- The edgeless graph on 3 vertices has no edges. -/
@[category test, AMS 5]
example : (⊥ : SimpleGraph (Fin 3)).edgeFinset.card = 0 := by decide +native

end WrittenOnTheWallII.GraphConjecture34
