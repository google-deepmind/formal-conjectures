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
# Erdős Problem 773

*Reference:* [erdosproblems.com/773](https://www.erdosproblems.com/773)

A question of Alon and Erdős [AlEr85], who proved $|A| \geq N^{2/3-o(1)}$ is possible
(via a random subset), and observed that $|A| \ll N / (\log N)^{1/4}$, since (as shown
by Landau) the density of the sums of two squares decays like $(\log N)^{-1/2}$.
The lower bound was improved to $|A| \gg N^{2/3}$ by Lefmann and Thiele [LeTh95].

[AlEr85] Alon, N. and Erdős, P., *On the size of the largest Sidon subset of a random set of integers*, 1985.

[LeTh95] Lefmann, H. and Thiele, T., *Point sets with distinct distances*, 1995.
-/

namespace Erdos773

/-- A finite set of natural numbers is a Sidon set if all pairwise sums are distinct. -/
def IsSidonSet (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- The set of perfect squares $\{1^2, 2^2, \ldots, N^2\}$. -/
def squaresUpTo (N : ℕ) : Finset ℕ :=
  (Finset.range N).image (fun i => (i + 1) ^ 2)

/--
Is the size of the largest Sidon subset of $\{1^2, 2^2, \ldots, N^2\}$ equal to
$N^{1-o(1)}$? That is, for every $\varepsilon > 0$, for all sufficiently large $N$,
there exists a Sidon subset of $\{1^2, 2^2, \ldots, N^2\}$ of size at least
$N^{1-\varepsilon}$.

Known bounds:
- Lower: $|A| \gg N^{2/3}$ (Lefmann–Thiele [LeTh95])
- Upper: $|A| \ll N / (\log N)^{1/4}$ (Alon–Erdős [AlEr85])
-/
@[category research open, AMS 5 11]
theorem erdos_773 : answer(sorry) ↔
    ∀ ε : ℝ, ε > 0 →
      ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
        ∃ A : Finset ℕ, A ⊆ squaresUpTo N ∧ IsSidonSet A ∧
          (A.card : ℝ) ≥ (N : ℝ) ^ (1 - ε) := by
  sorry

end Erdos773
