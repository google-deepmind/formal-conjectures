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
# Erdős Problem 1087

Estimate the number of degenerate 4-element subsets of an $n$-point set in the plane,
where a 4-element subset is degenerate if some two distinct pairs determine the same distance.

*Reference:* [erdosproblems.com/1087](https://www.erdosproblems.com/1087)

[ErPu71] Erdős, P. and Purdy, G., _Some extremal problems in geometry_.
-/

open Classical

namespace Erdos1087

/-- A 4-element point set in $\mathbb{R}^2$ has a repeated distance if there exist two distinct
    unordered pairs of points determining the same distance. -/
def HasRepeatedDistance (S : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S,
    a ≠ b ∧ c ≠ d ∧ (a ≠ c ∨ b ≠ d) ∧ (a ≠ d ∨ b ≠ c) ∧ dist a b = dist c d

/-- The number of "degenerate" 4-element subsets (those with a repeated distance)
    of a point set $P$ in $\mathbb{R}^2$. -/
noncomputable def degenerateQuadrupleCount (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (P.powerset.filter (fun S => S.card = 4 ∧ HasRepeatedDistance S)).card

/--
Erdős Problem 1087 (Erdős–Purdy [ErPu71]):

Let $f(n)$ be minimal such that every set of $n$ points in $\mathbb{R}^2$ contains at most $f(n)$
"degenerate" 4-element subsets, where a 4-element subset is degenerate if some two
distinct pairs determine the same distance. Is it true that $f(n) \leq n^{3+o(1)}$?

Known bounds: $n^3 \log n \ll f(n) \ll n^{7/2}$.

Formally: for every $\varepsilon > 0$ there exists $N$ such that for all $n \geq N$ and every set $P$
of $n$ points in $\mathbb{R}^2$, the number of degenerate quadruples is at most $n^{3+\varepsilon}$.
-/
@[category research open, AMS 5 52]
theorem erdos_1087 : answer(sorry) ↔
    ∀ (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
        P.card = n →
        (degenerateQuadrupleCount P : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) + ε) := by
  sorry

end Erdos1087
