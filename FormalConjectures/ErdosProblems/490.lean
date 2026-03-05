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
# Erdős Problem 490

If $A, B \subseteq \{1, \ldots, N\}$ are such that all products $ab$ ($a \in A$, $b \in B$)
are distinct, is it true that $|A| \cdot |B| \ll N^2 / \log N$?

*Reference:* [erdosproblems.com/490](https://www.erdosproblems.com/490)

[Sz76] Szemerédi, E., *On the number of edges in products of sets of integers*. 1976.
-/

namespace Erdos490

/--
The products $ab$ with $a \in A$ and $b \in B$ are all distinct: the multiplication
map $A \times B \to \mathbb{N}$ is injective.
-/
def HasDistinctProducts (A B : Finset ℕ) : Prop :=
  ∀ a₁ ∈ A, ∀ b₁ ∈ B, ∀ a₂ ∈ A, ∀ b₂ ∈ B,
    a₁ * b₁ = a₂ * b₂ → a₁ = a₂ ∧ b₁ = b₂

/--
If $A, B \subseteq \{1, \ldots, N\}$ are such that all products $ab$ ($a \in A$, $b \in B$)
are distinct, then $|A| \cdot |B| \ll N^2 / \log N$.

Formally: there exists a constant $C > 0$ such that for all $N$ and all
$A, B \subseteq \{1, \ldots, N\}$ with distinct products,
$$
  |A| \cdot |B| \le C \cdot \frac{N^2}{\log N}.
$$

Proved by Szemerédi [Sz76].
-/
@[category research solved, AMS 5 11]
theorem erdos_490 :
    ∃ C : ℝ, C > 0 ∧
      ∀ (N : ℕ) (A B : Finset ℕ),
        (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
        (∀ b ∈ B, 1 ≤ b ∧ b ≤ N) →
        HasDistinctProducts A B →
        (A.card : ℝ) * (B.card : ℝ) ≤ C * ((N : ℝ) ^ 2 / Real.log (N : ℝ)) := by
  sorry

end Erdos490
