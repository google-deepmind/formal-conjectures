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
# Erdős Problem 829

*Reference:* [erdosproblems.com/829](https://www.erdosproblems.com/829)

Let $A \subset \mathbb{N}$ be the set of cubes. Is it true that
$1_A * 1_A(n) \ll (\log n)^{O(1)}$?

Here $1_A * 1_A(n)$ counts the number of representations of $n$ as a sum of two
positive cubes, i.e., the number of pairs $(a, b)$ with $a^3 + b^3 = n$.

Mordell proved that $\limsup 1_A * 1_A(n) = \infty$. Mahler [Ma35b] proved
$1_A * 1_A(n) \gg (\log n)^{1/4}$ for infinitely many $n$. Stewart [St08] improved
this to $1_A * 1_A(n) \gg (\log n)^{11/13}$.
-/

open Real Finset

namespace Erdos829

/-- The number of representations of $n$ as a sum of two positive cubes:
$|\{(a, b) \in \mathbb{N} \times \mathbb{N} : a \geq 1 \land b \geq 1 \land a^3 + b^3 = n\}|$. -/
def sumOfTwoCubesRepr (n : ℕ) : ℕ :=
  ((Finset.range n).product (Finset.range n)).filter
    (fun p => p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 ^ 3 + p.2 ^ 3 = n) |>.card

/--
**Erdős Problem 829** [Er83]:

Is it true that the number of representations of $n$ as a sum of two positive cubes is bounded
by a polynomial in $\log n$? That is, do there exist constants $C > 0$ and $k > 0$
such that for all sufficiently large $n$,
$$\operatorname{sumOfTwoCubesRepr}(n) \leq C \cdot (\log n)^k?$$
-/
@[category research open, AMS 11]
theorem erdos_829 : answer(sorry) ↔
    ∃ C : ℝ, C > 0 ∧ ∃ k : ℝ, k > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (sumOfTwoCubesRepr n : ℝ) ≤ C * (Real.log n) ^ k := by
  sorry

end Erdos829
