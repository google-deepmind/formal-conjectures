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

[ErSa87] Erdős, P. and Sárközy, A., _On divisibility properties of integers of the form
a + a'_. Acta Math. Hungar. (1987), 117–122.

[Sa92c] Sárközy, G. N., _On a problem of P. Erdős_. Acta Math. Hungar. (1992), 271–282.

[Gy01] Gyarmati, K., _On divisibility properties of integers of the form ab + 1_. Period. Math.
Hungar. (2001), 71–79.

[Ko04] Konyagin, S. V., _Problems of the set of square-free numbers_. Izv. Ross. Akad. Nauk
Ser. Mat. (2004), 63–90.

OEIS: A392164, A392165
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

See also `erdos_1103` for the infinite analogue; upper bounds for this problem directly
imply lower bounds for Problem 1103.
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

/--
Weaker variant of `erdos_1109`: is $f(N) \leq N^{o(1)}$, i.e., does $f(N)$ grow
sub-polynomially? This asks whether for every $\varepsilon > 0$, we have
$f(N) \leq N^\varepsilon$ for all sufficiently large $N$.

This is implied by the stronger polylogarithmic conjecture `erdos_1109`, but may be
more tractable.
-/
@[category research open, AMS 5 11]
theorem erdos_1109_subpolynomial :
    answer(sorry) ↔
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset ℕ,
      (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
      (∀ n ∈ A + A, Squarefree n) →
      (A.card : ℝ) ≤ (N : ℝ) ^ ε := by
  sorry

end Erdos1109
