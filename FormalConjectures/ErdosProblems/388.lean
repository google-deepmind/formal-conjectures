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
# Erdős Problem 388

*Reference:* [erdosproblems.com/388](https://www.erdosproblems.com/388)

Can one classify all solutions of
$$\prod_{1 \le i \le k_1} (m_1 + i) = \prod_{1 \le j \le k_2} (m_2 + j)$$
where $k_1, k_2 > 3$ and $m_1 + k_1 \le m_2$? Are there only finitely many solutions?

More generally, if $k_1 > 2$ then for fixed $a$ and $b$,
$$a \cdot \prod_{1 \le i \le k_1} (m_1 + i) = b \cdot \prod_{1 \le j \le k_2} (m_2 + j)$$
should have only a finite number of solutions.

See also problems 363 and 931.

[Er76d] Erdős, P.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).

[Er92e] Erdős, P.
-/

open Finset BigOperators

namespace Erdos388

/-- The product of $k$ consecutive natural numbers starting from $m + 1$:
$(m+1)(m+2)\cdots(m+k)$. -/
def consecutiveProduct (m k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, (m + 1 + i)

/--
Erdős Problem 388 [Er76d] [ErGr80] [Er92e]:

Are there only finitely many 4-tuples $(m_1, k_1, m_2, k_2)$ of natural numbers
with $k_1, k_2 > 3$ and $m_1 + k_1 \le m_2$ such that
$$(m_1+1)(m_1+2)\cdots(m_1+k_1) = (m_2+1)(m_2+2)\cdots(m_2+k_2)?$$
-/
@[category research open, AMS 11]
theorem erdos_388 :
    answer(sorry) ↔
    Set.Finite {t : ℕ × ℕ × ℕ × ℕ |
      3 < t.2.1 ∧ 3 < t.2.2.2 ∧
      t.1 + t.2.1 ≤ t.2.2.1 ∧
      consecutiveProduct t.1 t.2.1 = consecutiveProduct t.2.2.1 t.2.2.2} := by
  sorry

/--
Erdős Problem 388 (General conjecture) [Er76d] [ErGr80] [Er92e]:

For $k_1 > 2$ and fixed $a, b$, the equation
$$a \cdot \prod_{1 \le i \le k_1} (m_1 + i) = b \cdot \prod_{1 \le j \le k_2} (m_2 + j)$$
should have only finitely many solutions.
-/
@[category research open, AMS 11]
theorem erdos_388.variants.general :
    answer(sorry) ↔
    ∀ (a b : ℕ) (k₁ : ℕ), 2 < k₁ →
    ∀ k₂ : ℕ,
    Set.Finite {t : ℕ × ℕ |
      a * consecutiveProduct t.1 k₁ = b * consecutiveProduct t.2 k₂} := by
  sorry

end Erdos388
