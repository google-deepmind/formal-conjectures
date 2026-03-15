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
# Erdős Problem 343

If a multiset of positive integers has positive lower density, must it be subcomplete?
That is, must its set of finite subset sums contain an infinite arithmetic progression?
Proved by Szemerédi and Vu.

*Reference:* [erdosproblems.com/343](https://www.erdosproblems.com/343)

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).

[SzVu06] Szemerédi, E. and Vu, V.H., *Long arithmetic progressions in sumsets: thresholds and
bounds*. Journal of the American Mathematical Society (2006), 119-169.

[Fo66] Folkman, J., *On the representation of integers as sums of distinct terms from a fixed
sequence*. Canadian Journal of Mathematics (1966), 643-655.
-/

open scoped BigOperators

namespace Erdos343

/-- The counting function for a multiset represented by multiplicities:
number of elements (with multiplicity) in $\{1, \ldots, N\}$. -/
def countUpTo (mult : ℕ → ℕ) (N : ℕ) : ℕ :=
  ∑ k ∈ Finset.range N, mult (k + 1)

/-- The set of all finite subset sums $P(A)$ of a multiset.
A finite submultiset is $b : \mathbb{N} \to_0 \mathbb{N}$ with $b(n) \leq \mathrm{mult}(n)$
for all $n$. The sum is $\sum n \cdot b(n)$. -/
def subsetSums (mult : ℕ → ℕ) : Set ℕ :=
  {s : ℕ | ∃ (b : ℕ →₀ ℕ), (∀ n, b n ≤ mult n) ∧ s = b.sum (fun n k => n * k)}

/-- A set of natural numbers contains an infinite arithmetic progression
$\{a + nd : n \in \mathbb{N}\}$ for some $a \geq 0$ and $d > 0$. -/
def ContainsInfiniteAP (S : Set ℕ) : Prop :=
  ∃ (a d : ℕ), 0 < d ∧ ∀ n : ℕ, a + n * d ∈ S

/--
Erdős Problem 343 [ErGr80, p.54]:

If $A \subseteq \mathbb{N}$ is a multiset of integers such that
$|A \cap \{1, \ldots, N\}| \gg N$ for all $N$, must $A$ be subcomplete?
That is, must $P(A) = \{\sum_{n \in B} n : B \subseteq A \text{ finite}\}$
contain an infinite arithmetic progression?

A problem of Folkman. Proved by Szemerédi and Vu [SzVu06].
-/
@[category research solved, AMS 5 11]
theorem erdos_343 :
    answer(True) ↔
      ∀ (mult : ℕ → ℕ),
        mult 0 = 0 →
        (∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 0 < N → c * (N : ℝ) ≤ (countUpTo mult N : ℝ)) →
        ContainsInfiniteAP (subsetSums mult) := by
  sorry

end Erdos343
