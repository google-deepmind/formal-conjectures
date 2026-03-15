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
# Erdős Problem 798

*Reference:* [erdosproblems.com/798](https://www.erdosproblems.com/798)

Let $t(n)$ be the minimum number of points in $\{1, \ldots, n\}^2$ such that the $\binom{t}{2}$
lines determined by these points cover all points in $\{1, \ldots, n\}^2$.

Estimate $t(n)$. In particular, is it true that $t(n) = o(n)$?

A problem of Erdős and Purdy, who proved $t(n) \gg n^{2/3}$.
Resolved by Alon [Al91] who proved $t(n) \ll n^{2/3} \log n$, confirming $t(n) = o(n)$.

[Al91] Alon, N., _Economical coverings of sets of lattice points_. Geom. Funct. Anal. (1991), 224–230.
-/

namespace Erdos798

/-- Three points in $\mathbb{Z} \times \mathbb{Z}$ are collinear if the cross product of the
displacement vectors from the first point is zero. -/
def IntGridCollinear (p q r : ℤ × ℤ) : Prop :=
  (q.1 - p.1) * (r.2 - p.2) = (r.1 - p.1) * (q.2 - p.2)

/-- A finite set $S$ of points in $\{1, \ldots, n\}^2$ covers the grid if every point
in $\{1, \ldots, n\}^2$ lies on a line determined by two distinct points of $S$. -/
def CoversIntGrid (n : ℕ) (S : Finset (ℤ × ℤ)) : Prop :=
  (∀ p ∈ S, 1 ≤ p.1 ∧ p.1 ≤ ↑n ∧ 1 ≤ p.2 ∧ p.2 ≤ ↑n) ∧
  ∀ (p : ℤ × ℤ), 1 ≤ p.1 → p.1 ≤ ↑n → 1 ≤ p.2 → p.2 ≤ ↑n →
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ IntGridCollinear a b p

/-- $t(n)$: the minimum number of points in $\{1, \ldots, n\}^2$ whose pairwise lines
cover all $n^2$ grid points. -/
noncomputable def gridCoveringNumber (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ S : Finset (ℤ × ℤ), S.card = k ∧ CoversIntGrid n S}

/--
Erdős Problem 798 (proved by Alon [Al91]):

$t(n) = o(n)$, i.e., the minimum number of points in $\{1, \ldots, n\}^2$ whose lines
cover all grid points is sublinear in $n$.

Equivalently: for every $\varepsilon > 0$, there exists $N_0$ such that for all $n \geq N_0$,
$t(n) \leq \varepsilon \cdot n$.
-/
@[category research solved, AMS 5 52]
theorem erdos_798 :
    answer(True) ↔
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (gridCoveringNumber n : ℝ) ≤ ε * (n : ℝ) := by
  sorry

/--
Erdős–Purdy lower bound for Problem 798:

$t(n) \gg n^{2/3}$, i.e., there exists a constant $C > 0$ such that
$t(n) \geq C \cdot n^{2/3}$ for all sufficiently large $n$.
-/
@[category research solved, AMS 5 52]
theorem erdos_798_lower :
    ∃ C : ℝ, C > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (gridCoveringNumber n : ℝ) ≥ C * (n : ℝ) ^ ((2 : ℝ) / 3) := by
  sorry

/--
Alon's upper bound for Problem 798 [Al91]:

$t(n) \ll n^{2/3} \log n$, i.e., there exists a constant $C > 0$ such that
$t(n) \leq C \cdot n^{2/3} \cdot \log n$ for all sufficiently large $n$.

This is the result that implies $t(n) = o(n)$.
-/
@[category research solved, AMS 5 52]
theorem erdos_798_upper :
    ∃ C : ℝ, C > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (gridCoveringNumber n : ℝ) ≤ C * (n : ℝ) ^ ((2 : ℝ) / 3) * Real.log n := by
  sorry

end Erdos798
