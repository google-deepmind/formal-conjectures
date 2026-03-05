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
# Erdős Problem 861

*Reference:* [erdosproblems.com/861](https://www.erdosproblems.com/861)

Let $f(N)$ be the size of the largest Sidon subset of $\{1,\ldots,N\}$ and $A(N)$ be
the number of Sidon subsets of $\{1,\ldots,N\}$. Is it true that
$$A(N)/2^{f(N)}\to \infty?$$
Is it true that $A(N) = 2^{(1+o(1))f(N)}$?

A problem of Cameron and Erdős [Er92c]. The first question is answered positively and the
second negatively. The current best bounds (for large $N$) are
$$2^{1.16\,f(N)} \leq A(N) \leq 2^{6.442\,f(N)}.$$
The lower bound is due to Saxton–Thomason [SaTh15]; the upper bound is due to
Kohayakawa–Lee–Rödl–Samotij [KLRS15].

[Er92c] Erdős, P., *Some of my favourite problems in number theory, combinatorics, and geometry*,
Resenhas (1995).

[SaTh15] Saxton, D. and Thomason, A., *The number of Sidon sets and the maximum size of Sidon
sets contained in a sparse random set of integers* (2015).

[KLRS15] Kohayakawa, Y., Lee, S. J., Rödl, V., and Samotij, W., *The number of Sidon sets and
the maximum size of Sidon sets contained in a sparse random set of integers* (2015).
-/

open scoped Classical

open Finset Filter

namespace Erdos861

/-- A finite set of natural numbers is a Sidon set if all pairwise sums are distinct. -/
def IsSidonSet (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- $f(N)$, the cardinality of the largest Sidon subset of $\{1, \ldots, N\}$. -/
noncomputable def maxSidonSize (N : ℕ) : ℕ :=
  ((Icc 1 N).powerset.filter IsSidonSet).sup Finset.card

/-- $A(N)$, the number of Sidon subsets of $\{1, \ldots, N\}$. -/
noncomputable def countSidonSubsets (N : ℕ) : ℕ :=
  ((Icc 1 N).powerset.filter IsSidonSet).card

/--
Erdős Problem 861, first question (Cameron–Erdős [Er92c], proved):

$A(N) / 2^{f(N)} \to \infty$ as $N \to \infty$.
-/
@[category research solved, AMS 5 11]
theorem erdos_861 : answer(True) ↔
    Tendsto (fun N => (countSidonSubsets N : ℝ) / (2 : ℝ) ^ (maxSidonSize N))
      atTop atTop := by
  sorry

/--
Erdős Problem 861, lower bound (Saxton–Thomason [SaTh15]):

For all sufficiently large $N$,
$A(N) \geq 2^{1.16 \cdot f(N)}$.
-/
@[category research solved, AMS 5 11]
theorem erdos_861.variants.lower :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      (countSidonSubsets N : ℝ) ≥ (2 : ℝ) ^ ((1.16 : ℝ) * (maxSidonSize N : ℝ)) := by
  sorry

/--
Erdős Problem 861, upper bound (Kohayakawa–Lee–Rödl–Samotij [KLRS15]):

For all sufficiently large $N$,
$A(N) \leq 2^{6.442 \cdot f(N)}$.
-/
@[category research solved, AMS 5 11]
theorem erdos_861.variants.upper :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      (countSidonSubsets N : ℝ) ≤ (2 : ℝ) ^ ((6.442 : ℝ) * (maxSidonSize N : ℝ)) := by
  sorry

end Erdos861
