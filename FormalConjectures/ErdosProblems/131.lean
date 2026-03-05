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
# Erdős Problem 131

*Reference:* [erdosproblems.com/131](https://www.erdosproblems.com/131)

Let $F(N)$ be the maximal size of $A \subseteq \{1, \ldots, N\}$ such that no $a \in A$ divides
the sum of any distinct elements of $A \setminus \{a\}$. Estimate $F(N)$.

The specific question "is $F(N) > N^{1/2 - o(1)}$?" has been answered NO by
Pham and Zakharov, who proved $F(N) \leq N^{1/4 + o(1)}$ via non-averaging sets.
The correct growth rate of $F(N)$ remains open.

Known bounds: $N^{1/5} \ll F(N) \leq N^{1/4 + o(1)}$.

[Er75b] Erdős, P., *Problems and results on combinatorial number theory III*, 1975.

[Er97b] Erdős, P., *Some of my new and almost new problems and results in combinatorial
number theory*, 1997.

[ELRSS99] Erdős, P., Lev, V., Rauzy, G., Sándor, C., Sárközy, A., *Greedy algorithm,
arithmetic progressions, subset sums and divisibility*, 1999.

[PhZa24] Pham, T., Zakharov, D., *Non-averaging sets and the Erdős divisibility conjecture*,
2024.
-/

open Filter

namespace Erdos131

/-- A finite set $A \subseteq \mathbb{N}$ is *non-dividing* if for every $a \in A$ and every
nonempty $S \subseteq A \setminus \{a\}$, the element $a$ does not divide $\sum_{s \in S} s$. -/
def IsNonDividing (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ S : Finset ℕ, S ⊆ A.erase a → S.Nonempty → ¬(a ∣ S.sum id)

/-- $F(N)$ is the maximal cardinality of a non-dividing subset of $\{1, \ldots, N\}$. -/
noncomputable def erdos131F (N : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsNonDividing A ∧ A.card = k}

/--
Erdős Problem 131 [Er75b, Er97b]:
Let $F(N)$ be the maximal size of a non-dividing subset of $\{1, \ldots, N\}$.
The open problem is to determine the correct polynomial growth rate of $F(N)$.

Known bounds:
- $F(N) \geq c \cdot N^{1/5}$ (Csaba; Erdős–Lev–Rauzy–Sándor–Sárközy [ELRSS99])
- $F(N) \leq N^{1/4 + o(1)}$ (Pham–Zakharov [PhZa24], via non-averaging sets)

This conjecture asserts that the Pham–Zakharov upper bound is essentially tight:
$F(N) \geq N^{1/4 - \varepsilon}$ for any $\varepsilon > 0$ and all sufficiently large $N$.
-/
@[category research open, AMS 5 11]
theorem erdos_131 :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, (erdos131F N : ℝ) ≥ (N : ℝ) ^ ((1 : ℝ) / 4 - ε) := by
  sorry

end Erdos131
