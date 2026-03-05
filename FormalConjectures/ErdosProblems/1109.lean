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
# Erdős Problem 1109

*Reference:* [erdosproblems.com/1109](https://www.erdosproblems.com/1109)

[ErSa87] Erdős, P. and Sárközy, A., *On the number of pairs of integers with
least common multiple not exceeding $x$*. (1987)

[Ko04] Konyagin, S. V. (2004)
-/

open Finset Pointwise Real

namespace Erdos1109

/--
Let $f(N)$ be the size of the largest subset $A \subseteq \{1, \ldots, N\}$ such that every
$n \in A + A$ is squarefree. Is it true that $f(N) \leq (\log N)^{O(1)}$?

Formalized as: there exist constants $C > 0$ and $k > 0$ such that for all
sufficiently large $N$, every subset $A \subseteq \{1, \ldots, N\}$ whose sumset $A + A$ is
entirely squarefree satisfies $|A| \leq C \cdot (\log N)^k$.

First studied by Erdős and Sárközy [ErSa87], who proved
$$\log N \ll f(N) \ll N^{3/4} \cdot \log N.$$
Konyagin [Ko04] improved this to
$$(\log \log N) \cdot (\log N)^2 \ll f(N) \ll N^{11/15 + o(1)}.$$
-/
@[category research open, AMS 5 11]
theorem erdos_1109 :
    answer(sorry) ↔
    ∃ C : ℝ, C > 0 ∧ ∃ k : ℕ, 0 < k ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset ℕ,
      (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
      (∀ n ∈ A + A, Squarefree n) →
      (A.card : ℝ) ≤ C * (Real.log N) ^ k := by
  sorry

end Erdos1109
