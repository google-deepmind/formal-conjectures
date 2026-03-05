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
# Erdős Problem 1096

*Reference:* [erdosproblems.com/1096](https://www.erdosproblems.com/1096)

For $1 < q < 1 + \varepsilon$ with $\varepsilon$ sufficiently small, consider the sums
$\sum_{i \in S} q^i$ over all finite $S \subseteq \mathbb{N}$, ordered by size. Is it true
that the gaps between consecutive elements tend to zero?

[EJK90] Erdős, P., Joó, I., and Komornik, V., *Characterization of the unique expansions
$1 = \sum q^{-n_i}$ and related problems*, Bull. Soc. Math. France (1990).

[GWNT91] Galambos, J., *Representations of real numbers by infinite series*, Lecture Notes
in Mathematics, Springer (1991).
-/

open Finset

namespace Erdos1096

/-- The set of all numbers expressible as $\sum_{i \in S} q^i$ for some finite set
$S \subseteq \mathbb{N}$. -/
noncomputable def powerSumSet (q : ℝ) : Set ℝ :=
  {x : ℝ | ∃ S : Finset ℕ, x = S.sum (fun i => q ^ i)}

/--
Erdős Problem 1096 [EJK90, GWNT91]:

Let $1 < q < 1 + \varepsilon$ and consider the set of numbers of the form $\sum_{i \in S} q^i$
(for all finite $S \subseteq \mathbb{N}$), ordered by size as $0 = x_1 < x_2 < \cdots$.

Is it true that, provided $\varepsilon > 0$ is sufficiently small, $x_{k+1} - x_k \to 0$?

Equivalently: there exists $\varepsilon > 0$ such that for all $q \in (1, 1+\varepsilon)$, the
gaps between consecutive elements of the power sum set tend to zero. We formalize this as:
for every $\delta > 0$, every sufficiently large element of the set has a successor
in the set within distance $\delta$.

Erdős and Joó speculate that the threshold may be $q_0 \approx 1.3247$, the real root
of $x^3 = x + 1$, i.e., the smallest Pisot–Vijayaraghavan number.
-/
@[category research open, AMS 11]
theorem erdos_1096 :
    answer(sorry) ↔
      ∃ ε : ℝ, 0 < ε ∧
        ∀ q : ℝ, 1 < q → q < 1 + ε →
          ∀ δ : ℝ, 0 < δ →
            ∃ M : ℝ, ∀ x ∈ powerSumSet q, M ≤ x →
              ∃ y ∈ powerSumSet q, x < y ∧ y - x < δ := by
  sorry

end Erdos1096
