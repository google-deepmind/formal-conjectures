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
# Erdős Problem 121

*Reference:* [erdosproblems.com/121](https://www.erdosproblems.com/121)

Let $F_k(N)$ be the size of the largest subset of $\{1, \ldots, N\}$ with no $k$ distinct
elements whose product is a perfect square. Erdős–Sós–Sárközy conjectured
$F_{2k+1}(N) = (1 - o(1))N$ for $k \geq 2$; disproved by Tao, who showed $F_k(N) \leq
(1 - c_k)N$ for all $k \geq 4$.

[Er94b] [Er97] [Er97e] [Er98] Erdős, P., various problems papers.

[ESS95] Erdős, P., Sárközy, A., and Sós, V. T., _On product representations of powers. I_.
European Journal of Combinatorics (1995), 567-588.

[Er38] Erdős, P., _On sequences of integers no one of which divides the product of two others
and on related problems_. Tomsk. Gos. Univ. Ucen Zap. (1938), 74-82.

[GrSo01] Granville, A. and Soundararajan, K., _The spectrum of multiplicative functions_.
Annals of Mathematics (2) (2001), 407-470.

[Ta24] Tao, T., _On product representations of squares_. arXiv:2405.11610 (2024).
-/

open scoped BigOperators

open Filter

namespace Erdos121

/-- A finset $A$ has the property that no $k$ distinct elements have a product that is
a perfect square. -/
def NoKSquareProduct (k : ℕ) (A : Finset ℕ) : Prop :=
  ∀ B : Finset ℕ, B ⊆ A → B.card = k → ¬IsSquare (∏ b ∈ B, b)

/-- $F(k, N)$ is the size of the largest subset $A$ of $\{1, \ldots, N\}$ such that
no $k$ distinct elements of $A$ have a product that is a perfect square. -/
noncomputable def F (k N : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ A.card = m ∧ NoKSquareProduct k A}

/--
Erdős Problem #121 [Er94b, Er97, Er97e, Er98] — DISPROVED

Let $F_k(N)$ be the size of the largest $A \subseteq \{1,\ldots,N\}$ such that the product
of no $k$ distinct elements of $A$ is a perfect square.

Conjectured by Erdős, Sós, and Sárközy [ESS95]: Is $F_{2k+1}(N) = (1 - o(1)) N$ for all
$k \geq 2$? Answered in the negative by Tao [Ta24].
-/
@[category research solved, AMS 5 11]
theorem erdos_121 : answer(False) ↔
    ∀ k : ℕ, 2 ≤ k →
      Tendsto (fun N => (F (2 * k + 1) N : ℝ) / (N : ℝ)) atTop (nhds 1) := by
  sorry

/--
Tao [Ta24] proved that for any $k \geq 4$ there exists a constant $c_k > 0$ such that
$F_k(N) \leq (1 - c_k + o(1)) N$, disproving the conjecture for all odd $k \geq 5$.
-/
@[category research solved, AMS 5 11]
theorem erdos_121.variants.tao_upper_bound :
    ∀ k : ℕ, 4 ≤ k →
    ∃ c : ℝ, 0 < c ∧
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c + ε) * N := by
  sorry

/--
Erdős–Sós–Sárközy [ESS95] proved that $F_2(N) = (6/\pi^2 + o(1)) N$.
That is, the largest subset of $\{1, \ldots, N\}$ with no two distinct elements whose product
is a perfect square has asymptotic density $6/\pi^2$.
-/
@[category research solved, AMS 5 11]
theorem erdos_121.variants.F2_asymptotic :
    Tendsto (fun N => (F 2 N : ℝ) / (N : ℝ)) atTop (nhds (6 / Real.pi ^ 2)) := by
  sorry

/--
Erdős–Sós–Sárközy [ESS95] proved that $F_3(N) = (1 - o(1)) N$.
That is, almost all of $\{1, \ldots, N\}$ can be taken while avoiding three distinct elements
whose product is a perfect square.
-/
@[category research solved, AMS 5 11]
theorem erdos_121.variants.F3_asymptotic :
    Tendsto (fun N => (F 3 N : ℝ) / (N : ℝ)) atTop (nhds 1) := by
  sorry

end Erdos121
