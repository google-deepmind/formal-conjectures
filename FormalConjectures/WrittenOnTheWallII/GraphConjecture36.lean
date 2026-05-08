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
# Written on the Wall II - Conjecture 36

**Verbatim statement (WOWII #36, status F):**
> If G is a simple connected graph, then path(G) ≥ 2rad(G)/dp(G)

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj36


*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture36

open Classical SimpleGraph

/-- `dp G` is the number of diametrical pairs of `G`: the number of unordered
pairs `{u, v}` of vertices at distance `diam(G)`.  -/
noncomputable def dp {α : Type*} [Fintype α] (G : SimpleGraph α) : ℕ :=
  (Finset.univ.filter
    (fun p : Sym2 α => p.lift ⟨fun u v => G.dist u v = G.diam ∧ u ≠ v,
      fun u v => by simp [SimpleGraph.dist_comm, ne_comm]⟩)).card

/--
WOWII [Conjecture 36](http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj36)
(status F, disproved):

For every finite simple connected graph `G`,
`path(G) ≥ 2 · rad(G) / dp(G)`,
where `path(G)` is the floor of the average distance of `G`,
`rad(G)` is the radius of `G`, and `dp(G)` is the number of *diametrical pairs*
of `G` — that is, the number of pairs of vertices at distance `diam(G)`.

This conjecture was **disproved** by Waller in Oct 2003 (counterexample:
path number 5, radius 3, dp 1). Following the upstream pattern established
in #3823 for Conjecture 23, we record the disproof using `answer(False) ↔ ...`.
The hypothesis `0 < dp G` is the well-definedness guard for the division.
-/
@[category research solved, AMS 5]
theorem conjecture36 : answer(False) ↔
    ∀ {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α],
      ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_ : G.Connected) (_ : 0 < dp G),
        (2 * G.radius.toNat : ℝ) / (dp G : ℝ) ≤ (path G : ℝ) := by
  sorry

-- Sanity checks

/-- The `path G` invariant is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ (path G : ℝ) := Nat.cast_nonneg _

end WrittenOnTheWallII.GraphConjecture36
