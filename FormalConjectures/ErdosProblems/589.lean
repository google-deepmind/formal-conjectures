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
# Erdős Problem 589

*Reference:* [erdosproblems.com/589](https://www.erdosproblems.com/589)

Let $g(n)$ be maximal such that in any set of $n$ points in $\mathbb{R}^2$ with no four
points on a line there exists a subset of $g(n)$ points with no three points
on a line. Estimate $g(n)$.

The trivial greedy algorithm gives $g(n) \gg n^{1/2}$. Füredi [Fu91b] proved
$n^{1/2} \log n \ll g(n) = o(n)$.
Balogh and Solymosi [BaSo18] improved the upper bound to
$g(n) \ll n^{5/6+o(1)}$.
-/

namespace Erdos589

/-- A finite set of points in $\mathbb{R}^2$ has at most $k$ points on any affine line.
Equivalently, no $k + 1$ points of $S$ are collinear (lie on a common
line $\{p \mid a \cdot p_0 + b \cdot p_1 = c\}$ for some $(a, b) \neq (0, 0)$). -/
def AtMostKOnAnyLine (k : ℕ) (S : Finset (Fin 2 → ℝ)) : Prop :=
  ∀ T : Finset (Fin 2 → ℝ), T ⊆ S → T.card = k + 1 →
    ¬∃ (a b c : ℝ), (a ≠ 0 ∨ b ≠ 0) ∧
      ∀ p : Fin 2 → ℝ, p ∈ T → a * p 0 + b * p 1 = c

/-- `erdos589_g n` is the largest $m$ such that every set of $n$ points in $\mathbb{R}^2$
with no four on a line contains a subset of at least $m$ points with no
three on a line. -/
noncomputable def erdos589_g (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∀ S : Finset (Fin 2 → ℝ),
    S.card = n → AtMostKOnAnyLine 3 S →
    ∃ T : Finset (Fin 2 → ℝ), T ⊆ S ∧ m ≤ T.card ∧ AtMostKOnAnyLine 2 T}

/--
Erdős Problem 589 (lower bound, Füredi [Fu91b]):

There exists a constant $C > 0$ such that for all sufficiently large $n$,
$\operatorname{erdos589\_g}(n) \geq C \sqrt{n} \log n$.
-/
@[category research solved, AMS 05 52]
theorem erdos_589 :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos589_g n : ℝ) ≥ C * Real.sqrt (↑n) * Real.log (↑n) := by
  sorry

/--
Erdős Problem 589 (upper bound, Balogh–Solymosi [BaSo18]):

For all $\varepsilon > 0$, there exists $C > 0$ such that for all sufficiently large $n$,
$\operatorname{erdos589\_g}(n) \leq C \cdot n^{5/6 + \varepsilon}$.
-/
@[category research solved, AMS 05 52]
theorem erdos_589.variants.upper_bound (ε : ℝ) (hε : ε > 0) :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos589_g n : ℝ) ≤ C * (↑n : ℝ) ^ ((5 : ℝ) / 6 + ε) := by
  sorry

end Erdos589
