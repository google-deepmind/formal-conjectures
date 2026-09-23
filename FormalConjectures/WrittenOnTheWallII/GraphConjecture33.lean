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
# Written on the Wall II - Conjecture 33

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture33

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
WOWII [Conjecture 33](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph $G$,
$\operatorname{path}(G) \ge \lceil 2 \operatorname{dist}\_{\operatorname{avg}}(M, V) \rceil$,
where $\operatorname{path}(G)$ is the number of vertices of a largest induced path of $G$,
$M$ is the set of maximum-degree vertices, and
$\operatorname{dist}\_{\operatorname{avg}}(M, V)$ is the average of all nonzero distances
$\operatorname{dist}\_G(m, v)$ with $m \in M$ and $v \in V$.

The conjecture is false: the source records an October 2005 counterexample with
$\operatorname{path}(G) = 7$ and $\operatorname{dist}\_{\operatorname{avg}}(M, V) = 3.56$.
-/
@[category research solved, AMS 5]
theorem conjecture33 : answer(False) ↔
    ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected),
      let M : Set α := {v | G.degree v = G.maxDegree}
      let distAvg : ℝ :=
        open scoped Classical in
        let pairs := (M.toFinset ×ˢ Finset.univ).filter (fun p => G.dist p.1 p.2 ≠ 0)
        (∑ p ∈ pairs, (G.dist p.1 p.2 : ℝ)) / pairs.card
      Int.ceil (2 * distAvg) ≤ (path G : ℤ) := by
  sorry

-- Sanity checks

/-- The `path G` invariant cast to ℤ is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ (path G : ℤ) := Int.natCast_nonneg _

/-- In `K₃`, the max degree is 2. -/
@[category test, AMS 5]
example : (⊤ : SimpleGraph (Fin 3)).maxDegree = 2 := by decide

end WrittenOnTheWallII.GraphConjecture33
