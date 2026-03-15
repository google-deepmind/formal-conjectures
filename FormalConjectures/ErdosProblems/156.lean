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
# Erdős Problem 156

*Reference:* [erdosproblems.com/156](https://www.erdosproblems.com/156)

A question of Erdős, Sárközy, and Sós [ESS94]. Ruzsa [Ru98b] constructed a maximal Sidon set
of size $\ll (N \log N)^{1/3}$, but whether $O(N^{1/3})$ is achievable remains open.

See also Problem 340, which concerns the greedy Sidon sequence specifically.

OEIS: [A382397](https://oeis.org/A382397)

[ESS94] Erdős, P., Sárközy, A., and Sós, V. T., _On Sum Sets of Sidon Sets, I_.
Journal of Number Theory (1994), 329–347.

[Ru98b] Ruzsa, I. Z., _A small maximal Sidon set_. Ramanujan Journal (1998), 55–58.
-/

open Filter Set

open scoped Topology Real

namespace Erdos156

/--
Erdős–Sárközy–Sós Conjecture (Problem 156) [ESS94]:

Does there exist a maximal Sidon set $A \subset \{1, \ldots, N\}$ of size $O(N^{1/3})$?

The greedy algorithm produces a maximal Sidon set of size $\gg N^{1/3}$ (this is known).
Ruzsa [Ru98b] constructed a maximal Sidon set of size $\ll (N \log N)^{1/3}$, which is
close but does not reach $O(N^{1/3})$.

Formalized as: there exists a constant $C > 0$ such that for all sufficiently large $N$,
there exists a maximal Sidon set $A \subseteq \{1, \ldots, N\}$ with
$|A| \leq C \cdot N^{1/3}$.
-/
@[category research open, AMS 5 11]
theorem erdos_156 : answer(sorry) ↔
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop,
        ∃ A : Set ℕ, A.IsMaximalSidonSetIn N ∧
          (A.ncard : ℝ) ≤ C * (N : ℝ) ^ ((1 : ℝ) / 3) := by
  sorry

/--
Ruzsa's upper bound (Problem 156) [Ru98b]:

Ruzsa constructed a maximal Sidon set of size $O((N \log N)^{1/3})$. This is the best
known upper bound on the minimum size of a maximal Sidon set in $\{1, \ldots, N\}$.
-/
@[category research solved, AMS 5 11]
theorem erdos_156_ruzsa_upper :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop,
        ∃ A : Set ℕ, A.IsMaximalSidonSetIn N ∧
          (A.ncard : ℝ) ≤ C * ((N : ℝ) * Real.log N) ^ ((1 : ℝ) / 3) := by
  sorry

/--
Lower bound on maximal Sidon sets (Problem 156):

Every maximal Sidon set in $\{1, \ldots, N\}$ has size $\gg N^{1/3}$. This is a known result
(the greedy algorithm witnesses this, but the bound holds for all maximal Sidon sets).
-/
@[category research solved, AMS 5 11]
theorem erdos_156_lower :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop,
        ∀ A : Set ℕ, A.IsMaximalSidonSetIn N →
          C * (N : ℝ) ^ ((1 : ℝ) / 3) ≤ (A.ncard : ℝ) := by
  sorry

end Erdos156
