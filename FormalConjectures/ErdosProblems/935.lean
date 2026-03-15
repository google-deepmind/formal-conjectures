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
# Erdős Problem 935

This problem concerns the powerful (2-full) part $Q_2$ of products of consecutive integers
$n(n+1)\cdots(n+\ell)$. It asks whether $Q_2 < n^{2+\varepsilon}$ for all sufficiently large $n$,
and whether $Q_2 / n^{\ell+1} \to 0$ as $n \to \infty$.

The second part is essentially the same (up to constants) as Problem 367.
The ABC conjecture implies a positive answer to the third question.

*Reference:* [erdosproblems.com/935](https://www.erdosproblems.com/935)

*See also:* [Problem 367](https://www.erdosproblems.com/367),
[OEIS A057521](https://oeis.org/A057521),
[OEIS A389244](https://oeis.org/A389244)

[Er76d] Erdős, P., _Problems and results on number theoretic properties of consecutive
integers and related questions_. Proceedings of the Fifth Manitoba Conference on Numerical
Mathematics (Univ. Manitoba, Winnipeg, Man., 1975) (1976), 25-44.

[Fe26] Feng, T. et al., _Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on
the Erdős Problems_. arXiv:2601.22401 (2026).
-/

open Finset

open scoped BigOperators Real

namespace Erdos935

/-- The powerful (2-full) part of a natural number $n$: the product of all prime
power factors $p^a$ where $a \geq 2$. -/
noncomputable def powerfulPart (n : ℕ) : ℕ :=
  (n.factorization.support.filter (fun p => 2 ≤ n.factorization p)).prod
    (fun p => p ^ n.factorization p)

/--
Erdős Problem 935, Part 1:

Is it true that for every $\varepsilon > 0$ and $\ell \geq 1$, if $n$ is sufficiently large then
$$Q_2(n(n+1)\cdots(n+\ell)) < n^{2+\varepsilon}?$$
-/
@[category research open, AMS 11]
theorem erdos_935 :
    answer(sorry) ↔
    ∀ ℓ : ℕ, 1 ≤ ℓ →
    ∀ ε : ℝ, 0 < ε →
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (powerfulPart (∏ i ∈ Finset.range (ℓ + 1), (n + i)) : ℝ) <
        (n : ℝ) ^ ((2 : ℝ) + ε) := by
  sorry

/--
Erdős Problem 935, Part 2 (resolved):

For every $\ell \geq 2$, $\limsup_{n \to \infty} Q_2(n(n+1)\cdots(n+\ell))/n^2 = \infty$.
This was proved via solutions to the Pell equation $x^2 - 8y^2 = 1$.
Formulated as: for every $M$ and $N$, there exists $n \geq N$ such that
$Q_2(n(n+1)\cdots(n+\ell)) > M \cdot n^2$.
-/
@[category research solved, AMS 11]
theorem erdos_935.variants.part2 :
    ∀ ℓ : ℕ, 2 ≤ ℓ →
    ∀ M : ℝ, ∀ N : ℕ,
    ∃ n : ℕ, N ≤ n ∧
      (powerfulPart (∏ i ∈ Finset.range (ℓ + 1), (n + i)) : ℝ) >
        M * ((n : ℝ) ^ (2 : ℕ)) := by
  sorry

/--
Erdős Problem 935, Part 3:

Is it true that for every $\ell \geq 2$,
$\lim_{n \to \infty} Q_2(n(n+1)\cdots(n+\ell))/n^{\ell+1} = 0$?
Formulated as: for every $\varepsilon > 0$,
$Q_2(n(n+1)\cdots(n+\ell)) < \varepsilon \cdot n^{\ell+1}$ for all sufficiently large $n$.

The ABC conjecture implies a positive answer to this question.
-/
@[category research open, AMS 11]
theorem erdos_935.variants.part3 :
    answer(sorry) ↔
    ∀ ℓ : ℕ, 2 ≤ ℓ →
    ∀ ε : ℝ, 0 < ε →
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (powerfulPart (∏ i ∈ Finset.range (ℓ + 1), (n + i)) : ℝ) <
        ε * ((n : ℝ) ^ ((ℓ : ℝ) + 1)) := by
  sorry

end Erdos935
