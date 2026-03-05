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
# Erdős Problem 300

*Reference:* [erdosproblems.com/300](https://www.erdosproblems.com/300)

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).

[Cr03] Croot, E., *On a coloring conjecture about unit fractions*. Annals of Mathematics (2003).

[LiSa24] Liu, J. and Sawhney, M., *On a conjecture of Erdős and Graham about Egyptian
fractions* (2024).
-/

open Finset BigOperators

namespace Erdos300

/-- A finset $A$ of positive integers is *Egyptian-1-free* if no nonempty subset
$S \subseteq A$ has $\sum_{n \in S} 1/n = 1$. -/
def Egyptian1Free (A : Finset ℕ) : Prop :=
  ∀ S : Finset ℕ, S ⊆ A → S.Nonempty → ∑ n ∈ S, (1 : ℝ) / (n : ℝ) ≠ 1

/--
Erdős Problem 300 [ErGr80] [LiSa24]:

Let $A(N)$ denote the maximal cardinality of $A \subseteq \{1, \ldots, N\}$ such that
$\sum_{n \in S} 1/n \neq 1$ for all nonempty $S \subseteq A$. Estimate $A(N)$.

Erdős and Graham believed $A(N) = (1 + o(1))N$. Croot [Cr03] disproved this, showing
the existence of some constant $c < 1$ such that $A(N) < cN$ for all large $N$. It is
trivial that $A(N) \geq (1 - 1/e + o(1))N$.

Liu and Sawhney [LiSa24] proved that $A(N) = (1 - 1/e + o(1))N$, resolving the problem.

We formalize the resolved statement: for every $\varepsilon > 0$, for all sufficiently large $N$,
(1) every Egyptian-1-free $A \subseteq \{1, \ldots, N\}$ has
$|A| \leq (1 - 1/e + \varepsilon)N$, and
(2) there exists an Egyptian-1-free $A \subseteq \{1, \ldots, N\}$ with
$|A| \geq (1 - 1/e - \varepsilon)N$.
-/
@[category research solved, AMS 5 11]
theorem erdos_300 :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (∀ (A : Finset ℕ), A ⊆ Finset.Icc 1 N → Egyptian1Free A →
          (A.card : ℝ) ≤ (1 - Real.exp (-1) + ε) * (N : ℝ)) ∧
        (∃ (A : Finset ℕ), A ⊆ Finset.Icc 1 N ∧ Egyptian1Free A ∧
          (A.card : ℝ) ≥ (1 - Real.exp (-1) - ε) * (N : ℝ)) := by
  sorry

end Erdos300
