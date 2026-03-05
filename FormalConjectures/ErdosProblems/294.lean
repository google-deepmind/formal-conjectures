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
# Erdős Problem 294

*Reference:* [erdosproblems.com/294](https://www.erdosproblems.com/294)

Let $N \geq 1$ and let $t(N)$ be the least integer $t$ such that there is no solution to
$$1 = 1/n_1 + \cdots + 1/n_k$$
with $t = n_1 < \cdots < n_k \leq N$. Estimate $t(N)$.

Erdős and Graham [ErGr80] showed $t(N) \ll N / \log N$, but had no idea of the true value
of $t(N)$.

Solved by Liu and Sawhney [LiSa24] (up to $(\log \log N)^{O(1)}$), who proved
$$\frac{N}{(\log N)(\log \log N)^3 (\log \log \log N)^{O(1)}} \ll t(N) \ll \frac{N}{\log N}.$$

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathématique (1980).

[LiSa24] Liu, J. and Sawhney, M., *Unit fractions* (2024).
-/

open Classical Real Finset

namespace Erdos294

/-- There exists a representation of $1$ as a sum of distinct unit fractions
$1/n_1 + \cdots + 1/n_k$ with $t = n_1 < \cdots < n_k \leq N$. Formally: there exists a
finite set $S \subseteq \{t, \ldots, N\}$ containing $t$ whose reciprocals sum to $1$. -/
def HasUnitFractionRepFrom (t N : ℕ) : Prop :=
  ∃ S : Finset ℕ, t ∈ S ∧ (∀ m ∈ S, t ≤ m) ∧ (∀ m ∈ S, m ≤ N) ∧
    (∀ m ∈ S, 1 ≤ m) ∧ (S.sum fun m => (1 : ℚ) / m) = 1

/-- $t(N)$: the least positive integer $t$ such that there is no unit fraction
representation of $1$ using distinct integers from $\{t, \ldots, N\}$ starting at $t$.
Returns $N + 1$ as a default if no such $t$ exists. -/
noncomputable def leastNoRep (N : ℕ) : ℕ :=
  if h : ∃ t : ℕ, 1 ≤ t ∧ ¬HasUnitFractionRepFrom t N then
    Nat.find h
  else
    N + 1

/--
Erdős Problem 294 — Upper bound (Erdős–Graham) [ErGr80]:

There exists a constant $C > 0$ such that $t(N) \leq C \cdot N / \log N$ for all
sufficiently large $N$.
-/
@[category research solved, AMS 11]
theorem erdos_294 :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (leastNoRep N : ℝ) ≤ C * (N : ℝ) / Real.log (N : ℝ) := by
  sorry

/--
Erdős Problem 294 — Lower bound (Liu–Sawhney) [LiSa24]:

There exist constants $c > 0$ and $K \geq 0$ such that for all sufficiently large $N$,
$$t(N) \geq c \cdot \frac{N}{(\log N) \cdot (\log \log N)^3 \cdot (\log \log \log N)^K}.$$
-/
@[category research solved, AMS 11]
theorem erdos_294.variants.lower :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c * (N : ℝ) / (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)) ^ 3 *
        Real.log (Real.log (Real.log (N : ℝ))) ^ K) ≤ (leastNoRep N : ℝ) := by
  sorry

end Erdos294
