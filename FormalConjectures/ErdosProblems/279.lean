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
# Erdős Problem 279

*Reference:* [erdosproblems.com/279](https://www.erdosproblems.com/279)

Let $k \geq 3$. Is there a choice of congruence classes $a_p \pmod{p}$ for every prime $p$
such that all sufficiently large integers can be written as $a_p + t \cdot p$ for some
prime $p$ and integer $t \geq k$?

Even the case $k = 3$ seems difficult. The conjecture may hold with the primes
replaced by any set $A \subseteq \mathbb{N}$ with $|A \cap [1,N]| \gg N / \log N$ and
$\sum_{n \in A, n \leq N} 1/n - \log \log N \to \infty$.

For $k = 1$ or $k = 2$, any set $A$ with $\sum_{n \in A} 1/n = \infty$ has this property.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).
-/

namespace Erdos279

/--
Erdős Problem 279 [ErGr80, p.29]:

For every $k \geq 3$, there exists a choice of congruence classes $a_p \pmod{p}$ for
every prime $p$ such that all sufficiently large integers $n$ can be represented as
$n = a_p + t \cdot p$ for some prime $p$ and integer $t \geq k$.
-/
@[category research open, AMS 11]
theorem erdos_279 : answer(sorry) ↔ ∀ (k : ℕ), 3 ≤ k →
    ∃ a : ℕ → ℤ,
      ∃ N₀ : ℤ, ∀ n : ℤ, N₀ ≤ n →
        ∃ p : ℕ, Nat.Prime p ∧
          ∃ t : ℤ, (k : ℤ) ≤ t ∧ n = a p + t * (p : ℤ) := by
  sorry

end Erdos279
