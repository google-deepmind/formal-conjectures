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
# Erdős Problem 875

*Reference:* [erdosproblems.com/875](https://www.erdosproblems.com/875)

A problem of Deshouillers and Erdős (an infinite version of problem #874).
-/

open Filter Finset BigOperators

namespace Erdos875

/-- The set of $r$-fold subset sums of a set $A \subseteq \mathbb{N}$: all sums
$a_1 + \cdots + a_r$ where $a_1, \ldots, a_r$ are $r$ distinct elements of $A$. -/
def rSubsetSumsInf (A : Set ℕ) (r : ℕ) : Set ℕ :=
  {s | ∃ S : Finset ℕ, (↑S : Set ℕ) ⊆ A ∧ S.card = r ∧ S.sum id = s}

/-- An infinite set $A \subseteq \mathbb{N}$ is *admissible* if the $r$-fold subset sums $S_r$ are
pairwise disjoint for all distinct $r_1 \neq r_2$ with $r_1, r_2 \geq 1$. -/
def IsAdmissibleInf (A : Set ℕ) : Prop :=
  ∀ r₁ r₂ : ℕ, 1 ≤ r₁ → 1 ≤ r₂ → r₁ ≠ r₂ →
    Disjoint (rSubsetSumsInf A r₁) (rSubsetSumsInf A r₂)

/--
Erdős Problem 875, part (a):

There exists an infinite admissible set $A = \{a_1 < a_2 < \cdots\}$ such that
$a_{n+1}/a_n \to 1$ as $n \to \infty$.

Formulated as: for every $\varepsilon > 0$, eventually $a(n+1) \leq (1 + \varepsilon) \cdot a(n)$.
-/
@[category research open, AMS 5 11]
theorem erdos_875 :
    ∃ a : ℕ → ℕ, StrictMono a ∧
      IsAdmissibleInf (Set.range a) ∧
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          (a (n + 1) : ℝ) ≤ (1 + ε) * (a n : ℝ) := by
  sorry

/--
Erdős Problem 875, part (b):

Determine for which $c > 0$ there exists an infinite admissible set
$A = \{a_1 < a_2 < \cdots\}$ such that $a_{n+1} - a_n \leq n^c$ for all sufficiently large $n$.

Formalized as: there exists $c > 0$ and an infinite admissible sequence whose
gaps satisfy $a(n+1) - a(n) \leq n^c$ eventually.
-/
@[category research open, AMS 5 11]
theorem erdos_875.variants.gap :
    ∃ c : ℝ, c > 0 ∧
    ∃ a : ℕ → ℕ, StrictMono a ∧
      IsAdmissibleInf (Set.range a) ∧
      ∀ᶠ n : ℕ in atTop,
        (a (n + 1) : ℝ) - (a n : ℝ) ≤ (n : ℝ) ^ c := by
  sorry

end Erdos875
