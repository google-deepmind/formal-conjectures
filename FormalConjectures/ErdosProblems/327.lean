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
# Erdős Problem 327

*Reference:* [erdosproblems.com/327](https://www.erdosproblems.com/327)

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).
-/

open Finset

namespace Erdos327

/-- A finite set $A$ of positive integers is *unit-fraction-pair-free* if there are
no distinct $a, b \in A$ satisfying $(a + b) \mid ab$, equivalently, no distinct
$a, b \in A$ such that $\frac{1}{a} + \frac{1}{b}$ is a unit fraction. -/
def UnitFractionPairFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬((a + b) ∣ (a * b))

/-- A finite set $A$ of positive integers satisfies the strong unit-fraction-pair
condition if there are no distinct $a, b \in A$ satisfying $(a + b) \mid 2ab$. -/
def StrongUnitFractionPairFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬((a + b) ∣ (2 * a * b))

/--
Erdős Problem 327 [ErGr80]: Suppose $A \subseteq \{1, \ldots, N\}$ is such that for all
distinct $a, b \in A$, $(a + b) \nmid ab$ (equivalently, $\frac{1}{a} + \frac{1}{b}$ is never
a unit fraction). The odd numbers in $\{1, \ldots, N\}$ give a set of size $\sim N/2$ with this
property. We conjecture the maximum size is $(\frac{1}{2} + o(1))N$.

Note: Wouter van Doorn has shown that the density cannot exceed $25/28$.
-/
@[category research open, AMS 5 11]
theorem erdos_327 :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ (A : Finset ℕ), A ⊆ Finset.Icc 1 N → UnitFractionPairFree A →
          (A.card : ℝ) ≤ (1 / 2 + ε) * (N : ℝ) := by
  sorry

/--
The odd numbers in $\{1, \ldots, N\}$ witness that there exists a `UnitFractionPairFree` subset
of size $\geq (\frac{1}{2} - \varepsilon) N$ for any $\varepsilon > 0$ and sufficiently
large $N$.
-/
@[category undergraduate, AMS 5 11]
theorem erdos_327.variants.lower_bound :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∃ (A : Finset ℕ), A ⊆ Finset.Icc 1 N ∧ UnitFractionPairFree A ∧
          (A.card : ℝ) ≥ (1 / 2 - ε) * (N : ℝ) := by
  sorry

/--
Erdős Problem 327, Part 2 [ErGr80]: If $a, b \in A$ with $a \neq b$ implies
$(a + b) \nmid 2ab$, must $|A| = o(N)$?
-/
@[category research open, AMS 5 11]
theorem erdos_327.variants.strong :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ (A : Finset ℕ), A ⊆ Finset.Icc 1 N → StrongUnitFractionPairFree A →
          (A.card : ℝ) ≤ ε * (N : ℝ) := by
  sorry

end Erdos327
