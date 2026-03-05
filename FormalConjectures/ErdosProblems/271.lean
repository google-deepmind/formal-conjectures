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
# Erdős Problem 271

Stanley sequences are constructed by starting from $\{0, n\}$ and greedily avoiding 3-term
arithmetic progressions. The Odlyzko–Stanley conjecture asserts a dichotomy on their growth rates:
every such sequence eventually grows either as $\Theta(k^{\log_2 3})$ or as $\Theta(k^2 / \log k)$.

*Reference:* [erdosproblems.com/271](https://www.erdosproblems.com/271)

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).
-/

namespace Erdos271

/--
A sequence $a : \mathbb{N} \to \mathbb{N}$ is a Stanley sequence starting from $\{0, n\}$ if:
1. $a(0) = 0$ and $a(1) = n$
2. $a$ is strictly increasing
3. The image is 3-AP-free: no three indices $i < j < k$ satisfy $a(i) + a(k) = 2 \cdot a(j)$
4. It is greedy: for every $m$ between consecutive terms $a(k)$ and $a(k+1)$ (with $k \geq 1$),
   adding $m$ to $\{a(0), \ldots, a(k)\}$ would create a 3-term AP
-/
def IsStanleySeq (n : ℕ) (a : ℕ → ℕ) : Prop :=
  a 0 = 0 ∧ a 1 = n ∧
  StrictMono a ∧
  (∀ i j k : ℕ, i < j → j < k → a i + a k ≠ 2 * a j) ∧
  (∀ k : ℕ, 1 ≤ k → ∀ m : ℕ, a k < m → m < a (k + 1) →
    ∃ i j : ℕ, i < j ∧ j ≤ k ∧ a i + m = 2 * a j)

/--
Erdős Problem 271 [ErGr80, p.22]:

Let $A(n) = \{a_0 < a_1 < \cdots\}$ be the Stanley sequence defined by $a_0 = 0$, $a_1 = n$,
and for $k \geq 1$, $a_{k+1}$ is the least positive integer such that $\{a_0, \ldots, a_{k+1}\}$
contains no three-term arithmetic progression.

Can the $a_k$ be explicitly determined? How fast do they grow?

The Odlyzko–Stanley conjecture asserts that every such sequence eventually
satisfies either $a_k = \Theta(k^{\log_2 3})$ or $a_k = \Theta(k^2 / \log k)$. The first growth
rate is known for $A(1)$, $A(3^k)$, and $A(2 \cdot 3^k)$. No sequence with the second growth
rate has been proven, though computational evidence suggests $A(4)$ may have this
growth. Moy proved the upper bound $a_k \leq (k-1)(k+2)/2 + n$ for all $k \geq 0$.
-/
@[category research open, AMS 5 11]
theorem erdos_271 (n : ℕ) (hn : 0 < n)
    (a : ℕ → ℕ) (ha : IsStanleySeq n a) :
    (∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∃ N₀ : ℕ, ∀ k : ℕ, N₀ ≤ k →
        C₁ * (k : ℝ) ^ (Real.log 3 / Real.log 2) ≤ (a k : ℝ) ∧
        (a k : ℝ) ≤ C₂ * (k : ℝ) ^ (Real.log 3 / Real.log 2))
    ∨
    (∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∃ N₀ : ℕ, ∀ k : ℕ, N₀ ≤ k →
        C₁ * (k : ℝ) ^ 2 / Real.log (k : ℝ) ≤ (a k : ℝ) ∧
        (a k : ℝ) ≤ C₂ * (k : ℝ) ^ 2 / Real.log (k : ℝ)) := by
  sorry

end Erdos271
