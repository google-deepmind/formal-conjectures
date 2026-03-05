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
# Erdős Problem 437

*Reference:* [erdosproblems.com/437](https://www.erdosproblems.com/437)

Let $1 \le a_1 < \cdots < a_k \le x$. How many of the partial products
$a_1, a_1 a_2, \ldots, a_1 \cdots a_k$ can be squares? Is it true that, for any
$\varepsilon > 0$, there can be more than $x^{1-\varepsilon}$ squares?

Erdős and Graham write it is 'trivial' that there are $o(x)$ many such squares,
although this is not quite trivial, using Siegel's theorem.

A positive answer follows from work of Bui, Pratt, and Zaharescu [BPZ24],
as noted by Tao.

[BPZ24] Bui, H. M., Pratt, K., and Zaharescu, A.
-/

open scoped BigOperators

namespace Erdos437

/-- The partial product of the first $j+1$ elements of a finite sequence
$a \colon \mathrm{Fin}\; k \to \mathbb{N}$, i.e., $a(0) \cdot a(1) \cdots a(j)$. -/
def partialProd {k : ℕ} (a : Fin k → ℕ) (j : Fin k) : ℕ :=
  ∏ i ∈ Finset.univ.filter (fun i : Fin k => i ≤ j), a i

/-- The count of indices $j \in \{0, \ldots, k-1\}$ for which the partial product
$a(0) \cdots a(j)$ is a perfect square. -/
def squareCount {k : ℕ} (a : Fin k → ℕ) : ℕ :=
  (Finset.univ.filter (fun j : Fin k => IsSquare (partialProd a j))).card

/-- Erdős Problem 437 (solved):
For any $\varepsilon > 0$ and all sufficiently large $x$, there exists a strictly
increasing sequence $1 \le a_1 < \cdots < a_k \le x$ such that more than
$x^{1-\varepsilon}$ of the partial products $a_1, a_1 a_2, \ldots, a_1 \cdots a_k$
are perfect squares.

Proved by Bui, Pratt, and Zaharescu [BPZ24], as noted by Tao. -/
@[category research solved, AMS 11]
theorem erdos_437 : answer(True) ↔ ∀ (ε : ℝ), 0 < ε →
    ∃ N : ℕ, ∀ x : ℕ, N ≤ x →
    ∃ (k : ℕ) (a : Fin k → ℕ),
      StrictMono a ∧
      (∀ i, 1 ≤ a i) ∧
      (∀ i, a i ≤ x) ∧
      (squareCount a : ℝ) > (x : ℝ) ^ ((1 : ℝ) - ε) := by
  sorry

end Erdos437
