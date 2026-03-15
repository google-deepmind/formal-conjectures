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
Pham and Zakharov, who proved $F(N) \leq N^{1/4 + o(1)}$ via non-averaging sets
(see also Problem 186 for non-averaging sets).
The correct growth rate of $F(N)$ remains open.

Known bounds:
- Straus: $F(N) > \exp((\sqrt{2/\log 2}+o(1))\sqrt{\log N})$
- Csaba [Er97b]: $F(N) \gg N^{1/5}$
- Erdős–Lev–Rauzy–Sándor–Sárközy [ELRSS99]: $F(N) < 3N^{1/2} + 1$
- Pham–Zakharov [PhZa24]: $F(N) \leq N^{1/4 + o(1)}$

OEIS: [A068063](https://oeis.org/A068063)

[Er75b] Erdős, P., *Problems and results on combinatorial number theory III*.
Journées Arithmétiques de Bordeaux (1975), 295–310.

[Er97b] Erdős, P., *Some of my new and almost new problems and results in combinatorial
number theory*. Discrete Mathematics (1997), 227–231.

[ELRSS99] Erdős, P., Lev, V., Rauzy, G., Sándor, C., Sárközy, A., *Greedy algorithm,
arithmetic progressions, subset sums and divisibility*. Discrete Mathematics (1999), 119–135.

[PhZa24] Pham, H. T., Zakharov, D., *Sharp bound for the Erdős-Straus non-averaging set
problem*. arXiv:2410.14624 (2024).

[Gu04] Guy, R., *Unsolved Problems in Number Theory*, 3rd ed. Springer, 2004, Problem C16.
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
- $F(N) \gg N^{1/5}$ (Csaba, cited in [Er97b])
- $F(N) \leq N^{1/4 + o(1)}$ (Pham–Zakharov [PhZa24], via non-averaging sets)

This conjecture asserts that the Pham–Zakharov upper bound is essentially tight:
$F(N) \geq N^{1/4 - \varepsilon}$ for any $\varepsilon > 0$ and all sufficiently large $N$.
-/
@[category research open, AMS 5 11]
theorem erdos_131 :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, (erdos131F N : ℝ) ≥ (N : ℝ) ^ ((1 : ℝ) / 4 - ε) := by
  sorry

/--
Pham–Zakharov upper bound [PhZa24]: $F(N) \leq N^{1/4 + \varepsilon}$ for any $\varepsilon > 0$
and all sufficiently large $N$. This is a proven result, established via the connection
to non-averaging sets (see Problem 186).
-/
@[category research solved, AMS 5 11]
theorem erdos_131_upper :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, (erdos131F N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4 + ε) := by
  sorry

/--
Csaba's lower bound (cited in [Er97b]): $F(N) \geq c \cdot N^{1/5}$ for some constant $c > 0$
and all sufficiently large $N$. This is a proven result.
-/
@[category research solved, AMS 5 11]
theorem erdos_131_lower :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N : ℕ in atTop, (erdos131F N : ℝ) ≥ c * (N : ℝ) ^ ((1 : ℝ) / 5) := by
  sorry

end Erdos131
