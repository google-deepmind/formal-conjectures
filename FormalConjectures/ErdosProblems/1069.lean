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
# Erdős Problem 1069

*Reference:* [erdosproblems.com/1069](https://www.erdosproblems.com/1069)

Given any $n$ points in $\mathbb{R}^2$, the number of $k$-rich lines (lines containing
$\ge k$ of the points) is $\ll n^2 / k^3$, provided $k \le \sqrt{n}$.

Conjectured by Erdős, Croft, and Purdy [Er87b]. Proved by Szemerédi and Trotter [SzTr83].

[Er87b] Erdős, P., _Some combinatorial and metric problems in geometry_,
Intuitive geometry (Siófok, 1985), 1987, pp. 167–177. (see p. 169)

[SzTr83] Szemerédi, E. and Trotter, W.T., _Extremal problems in discrete geometry_,
Combinatorica 3 (1983), 381–392.
-/

open scoped Classical

namespace Erdos1069

/-- A line in $\mathbb{R}^2$ (represented as `Fin 2 → ℝ`): a set of the form
$\{p + t \cdot d \mid t \in \mathbb{R}\}$ for some point $p$ and nonzero direction $d$. -/
def IsLine (L : Set (Fin 2 → ℝ)) : Prop :=
  ∃ (p d : Fin 2 → ℝ), d ≠ 0 ∧ L = {q : Fin 2 → ℝ | ∃ t : ℝ, q = p + t • d}

/-- The number of $k$-rich lines determined by a finite point set $S \subseteq \mathbb{R}^2$:
lines containing at least $k$ points of $S$. -/
noncomputable def numKRichLines (S : Finset (Fin 2 → ℝ)) (k : ℕ) : ℕ :=
  Set.ncard {L : Set (Fin 2 → ℝ) | IsLine L ∧ k ≤ (S.filter (· ∈ L)).card}

/--
Erdős Problem 1069 (Szemerédi–Trotter theorem) [Er87b], [SzTr83]:

There exists a constant $C > 0$ such that for any finite set $S$ of $n$ points in $\mathbb{R}^2$
and any integer $k$ with $2 \le k$ and $k^2 \le n$, the number of lines containing at
least $k$ points of $S$ is at most $C \cdot n^2 / k^3$.
-/
@[category research solved, AMS 5 52]
theorem erdos_1069 :
    ∃ C : ℝ, C > 0 ∧
    ∀ (S : Finset (Fin 2 → ℝ)) (k : ℕ),
      2 ≤ k → (k : ℝ) ^ 2 ≤ (S.card : ℝ) →
      (numKRichLines S k : ℝ) ≤ C * (S.card : ℝ) ^ 2 / (k : ℝ) ^ 3 := by
  sorry

end Erdos1069
