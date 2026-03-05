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
# Erdős Problem 733

*Reference:* [erdosproblems.com/733](https://www.erdosproblems.com/733)

Call a sequence $1 < X_1 \leq \cdots \leq X_m \leq n$ line-compatible if there is a set of $n$
points in $\mathbb{R}^2$ such that there are $m$ lines $\ell_1, \ldots, \ell_m$ containing at least
two points, and the number of points on $\ell_i$ is exactly $X_i$.

This is essentially the same as problem 607, but with multiplicities. See also problem 732.

Proved by Szemerédi and Trotter [SzTr83].

[Er81] Erdős, P., 1981.

[SzTr83] Szemerédi, E. and Trotter, W. T., _Extremal problems in discrete geometry_.
Combinatorica 3 (1983), 381–392.
-/

open Classical

namespace Erdos733

/-- Three points in $\mathbb{R}^2$ are collinear: the cross product of the displacement
vectors $(q - p)$ and $(r - p)$ vanishes. -/
def Collinear (p q r : ℝ × ℝ) : Prop :=
  (q.1 - p.1) * (r.2 - p.2) = (r.1 - p.1) * (q.2 - p.2)

/-- A line determined by a point set $P$: the set of all points in $P$ collinear
with a given pair of distinct points. -/
def IsLine (P : Finset (ℝ × ℝ)) (L : Finset (ℝ × ℝ)) : Prop :=
  L ⊆ P ∧ 2 ≤ L.card ∧
  ∃ p q : ℝ × ℝ, p ∈ P ∧ q ∈ P ∧ p ≠ q ∧
    L = P.filter (fun r => Collinear p q r)

/-- A multiset of natural numbers is line-compatible for $n$ if there exists a
point set $P$ of size $n$ in $\mathbb{R}^2$ whose collection of determined lines yields
that multiset of sizes. -/
def IsLineCompatible (n : ℕ) (M : Multiset ℕ) : Prop :=
  ∃ P : Finset (ℝ × ℝ), P.card = n ∧
    ∃ lines : Finset (Finset (ℝ × ℝ)),
      (∀ L ∈ lines, IsLine P L) ∧
      (∀ L, IsLine P L → L ∈ lines) ∧
      lines.val.map Finset.card = M

/-- The set of achievable line-compatible multisets for $n$-point configurations
in $\mathbb{R}^2$. -/
def achievableLineMultisets (n : ℕ) : Set (Multiset ℕ) :=
  {M | IsLineCompatible n M}

/--
**Erdős Problem 733** [Er81]:

There exists a constant $C > 0$ such that for all sufficiently large $n$, the number
of line-compatible sequences (multisets of line sizes from $n$-point configurations
in $\mathbb{R}^2$) is at most $\exp(C \cdot \sqrt{n})$.

Proved by Szemerédi and Trotter [SzTr83].
-/
@[category research solved, AMS 5 52]
theorem erdos_733 :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (achievableLineMultisets n).Finite ∧
      ((achievableLineMultisets n).ncard : ℝ) ≤
        Real.exp (C * Real.sqrt (n : ℝ)) := by
  sorry

end Erdos733
