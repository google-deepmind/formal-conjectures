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
# Erdős Problem 360

*Reference:* [erdosproblems.com/360](https://www.erdosproblems.com/360)

Determine the asymptotic order of growth of $f(n)$, the minimum number of classes needed to
partition $\{1, \ldots, n-1\}$ so that $n$ cannot be represented as a sum of distinct elements
from any single class.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).

[AlEr96] Alon, N. and Erdős, P., *Sure monochromatic subset sums*. Acta Arithmetica (1996), 269–272.

[Vu07] Vu, V.H., *Some new results on subset sums*. Journal of Number Theory (2007), 229–233.

[CFP21] Conlon, D., Fox, J. and Pham, H.T., *Sum-free partitions* (2021).
-/

open Finset

namespace Erdos360

/--
A coloring $c$ of $\{1, \ldots, n-1\}$ into $k$ colors is sum-free for $n$ if $n$ cannot be
expressed as a sum of distinct elements from any single color class.
-/
def SumFreeColoring (n k : ℕ) (c : ℕ → Fin k) : Prop :=
  ∀ j : Fin k, ∀ S : Finset ℕ,
    S ⊆ Icc 1 (n - 1) →
    (∀ x ∈ S, c x = j) →
    S.sum id ≠ n

/--
The minimum number of color classes needed so that $\{1, \ldots, n-1\}$ can be colored
into classes where $n$ is not a sum of distinct elements from any single class.
-/
noncomputable def minSumFreeClasses (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ c : ℕ → Fin k, SumFreeColoring n k c}

/--
Let $f(n)$ be minimal such that $\{1, \ldots, n-1\}$ can be partitioned into $f(n)$ classes
so that $n$ cannot be expressed as a sum of distinct elements from the same class.
Conlon, Fox, and Pham [CFP21] determined the order of growth up to a multiplicative constant:
$$
f(n) \asymp \frac{n^{1/3} \cdot (n / \varphi(n))}{(\log n)^{1/3} \cdot (\log \log n)^{2/3}}
$$

[ErGr80, p.59], [AlEr96], [Vu07], [CFP21]
-/
@[category research solved, AMS 5 11]
theorem erdos_360 :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      let g := (n : ℝ) ^ ((1 : ℝ) / 3) * ((n : ℝ) / (Nat.totient n : ℝ)) /
        (Real.log (n : ℝ) ^ ((1 : ℝ) / 3) *
         Real.log (Real.log (n : ℝ)) ^ ((2 : ℝ) / 3))
      C₁ * g ≤ (minSumFreeClasses n : ℝ) ∧
      (minSumFreeClasses n : ℝ) ≤ C₂ * g := by
  sorry

end Erdos360
