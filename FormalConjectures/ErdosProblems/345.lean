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
# Erdős Problem 345

Asks whether the threshold of completeness $T$ (the least $m$ such that all $n \ge m$ are
representable as a finite subset sum) satisfies $T(n^k) > T(n^{k+1})$ for infinitely many $k$.

*Reference:* [erdosproblems.com/345](https://www.erdosproblems.com/345)

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory_. Monographies de L'Enseignement Mathematique (1980).
-/

open Finset BigOperators

namespace Erdos345

/-- The set of all finite subset sums of a set $A \subseteq \mathbb{N}$. That is,
$P(A) = \{\sum_{n \in B} n : B \subseteq A, B \text{ finite}\}$. -/
def subsetSums (A : Set ℕ) : Set ℕ :=
  {s | ∃ (B : Finset ℕ), (↑B : Set ℕ) ⊆ A ∧ s = ∑ n ∈ B, n}

/-- The threshold of completeness $T(A)$: the least $m$ such that
all $n \ge m$ are in $P(A)$, the set of finite subset sums of $A$.
(Only meaningful for complete sequences.) -/
noncomputable def thresholdOfCompleteness (A : Set ℕ) : ℕ :=
  sInf {m : ℕ | ∀ n : ℕ, n ≥ m → n ∈ subsetSums A}

/-- The set of $k$-th powers of positive integers: $\{1^k, 2^k, 3^k, \ldots\}$. -/
def kthPowers (k : ℕ) : Set ℕ :=
  {m | ∃ n : ℕ, n ≥ 1 ∧ m = n ^ k}

/--
Erdős Problem 345 [ErGr80, p.55]:

Let $A \subseteq \mathbb{N}$ be a complete sequence, and define the threshold of completeness
$T(A)$ to be the least integer $m$ such that all $n \ge m$ are in
$P(A) = \{\sum_{n \in B} n : B \subseteq A, B \text{ finite}\}$.

Is it true that there are infinitely many $k$ such that $T(n^k) > T(n^{k+1})$?

Known values: $T(n) = 1$, $T(n^2) = 128$, $T(n^3) = 12758$, $T(n^4) = 5134240$,
and $T(n^5) = 67898771$.
-/
@[category research open, AMS 5 11]
theorem erdos_345 :
    answer(sorry) ↔ Set.Infinite {k : ℕ | thresholdOfCompleteness (kthPowers k) >
      thresholdOfCompleteness (kthPowers (k + 1))} := by
  sorry

end Erdos345
