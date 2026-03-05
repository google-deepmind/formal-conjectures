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
# Erdős Problem 272

*Reference:* [erdosproblems.com/272](https://www.erdosproblems.com/272)

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980), p. 20.

[SiSo81] Simonovits, M. and Sós, V., *Intersection theorems for subsets of integers*. European
Journal of Combinatorics (1981).

[Sz99] Szabó, T. (1999).
-/

open Finset

namespace Erdos272

/--
A finset of natural numbers is a non-empty finite arithmetic progression if it is
nonempty and equals $\{a, a+d, a+2d, \ldots, a+(n-1) \cdot d\}$ for some $a, d \in \mathbb{N}$
where $n = |S|$. When $|S| \geq 2$ this forces $d > 0$ (so elements are distinct).
-/
def IsNonEmptyFiniteAP (S : Finset ℕ) : Prop :=
  S.Nonempty ∧ ∃ (a d : ℕ), ∀ x, x ∈ S ↔ ∃ i, i < S.card ∧ x = a + i * d

/--
Erdős Problem 272 [ErGr80, p. 20]:

Let $N \geq 1$. What is the largest $t$ such that there are
$A_1, \ldots, A_t \subseteq \{1, \ldots, N\}$ with $A_i \cap A_j$ a non-empty arithmetic
progression for all $i \neq j$?

Simonovits and Sós [SiSo81] showed that $t \ll N^2$. Szabó [Sz99] proved that the
maximum $t$ equals $N^2/2 + O(N^{5/3} (\log N)^3)$, resolving the asymptotic question.

Szabó conjectures that the maximum $t$ satisfies $t = N^2/2 + O(N)$, i.e., there
exists a constant $C > 0$ such that the largest such $t$ differs from $N^2/2$ by at
most $C \cdot N$.

We formalize Szabó's conjecture: there exists $C > 0$ such that for all $N \geq 1$,
(1) every AP-intersecting family of subsets of $\{1,\ldots,N\}$ has size
$\leq N^2/2 + C \cdot N$, and
(2) there exists an AP-intersecting family of size $\geq N^2/2 - C \cdot N$.
-/
@[category research open, AMS 5]
theorem erdos_272 :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (∀ (𝓕 : Finset (Finset ℕ)),
        (∀ A ∈ 𝓕, A ⊆ Finset.Icc 1 N) →
        (∀ A ∈ 𝓕, ∀ B ∈ 𝓕, A ≠ B → IsNonEmptyFiniteAP (A ∩ B)) →
        (𝓕.card : ℝ) ≤ (N : ℝ) ^ 2 / 2 + C * (N : ℝ)) ∧
      (∃ (𝓕 : Finset (Finset ℕ)),
        (∀ A ∈ 𝓕, A ⊆ Finset.Icc 1 N) ∧
        (∀ A ∈ 𝓕, ∀ B ∈ 𝓕, A ≠ B → IsNonEmptyFiniteAP (A ∩ B)) ∧
        (𝓕.card : ℝ) ≥ (N : ℝ) ^ 2 / 2 - C * (N : ℝ)) := by
  sorry

end Erdos272
