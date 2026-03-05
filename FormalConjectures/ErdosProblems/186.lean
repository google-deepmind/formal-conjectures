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
# Erdős Problem 186

*Reference:* [erdosproblems.com/186](https://www.erdosproblems.com/186)

Let $F(N)$ be the maximal size of $A \subseteq \{1, \ldots, N\}$ which is 'non-averaging', so that
no $n \in A$ is the arithmetic mean of at least two other distinct elements in $A$.
What is the order of growth of $F(N)$?

Originally due to Straus. It is known that
$N^{1/4} \ll F(N) \ll N^{1/4+o(1)}$.
The lower bound is due to Bosznay [Bo89] and the upper bound to Pham and
Zakharov [PhZa24], improving an earlier bound of Conlon, Fox, and Pham [CFP23].
The original upper bound of Erdős and Sárközy [ErSa90] was $\ll (N \log N)^{1/2}$.

[Er73] Erdős, P., *Problems and results on combinatorial number theory*.

[Er75b] Erdős, P., *Problems and results on combinatorial number theory II*.

[Er77c] Erdős, P., *Problems and results on combinatorial number theory III*.

[ErGr79] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).

[Bo89] Bosznay, A. P., *On the lower estimation of non-averaging sets* (1989).

[ErSa90] Erdős, P. and Sárközy, A. (1990).

[CFP23] Conlon, D., Fox, J., and Pham, H. T. (2023).

[PhZa24] Pham, H. T. and Zakharov, D. (2024).
-/

open Filter

namespace Erdos186

/-- A finite set of natural numbers $A$ is *non-averaging* if no element $a \in A$ is
    the arithmetic mean of two or more distinct elements in $A \setminus \{a\}$. Equivalently,
    for every $a \in A$ and every $S \subseteq A \setminus \{a\}$ with $|S| \geq 2$,
    we have $|S| \cdot a \neq \sum S$. -/
def IsNonAveraging (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ S : Finset ℕ, S ⊆ A.erase a → 2 ≤ S.card → S.card * a ≠ S.sum id

/-- $F(N)$ is the maximal cardinality of a non-averaging subset of $\{1, \ldots, N\}$. -/
noncomputable def nonAvgMax (N : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsNonAveraging A ∧ A.card = k}

/--
Erdős Problem 186 [Er73, Er75b, Er77c, ErGr79, ErGr80]:

The maximal size $F(N)$ of a non-averaging subset of $\{1, \ldots, N\}$ satisfies
$F(N) = N^{1/4+o(1)}$, i.e., for every $\varepsilon > 0$,
$$N^{1/4-\varepsilon} \leq F(N) \leq N^{1/4+\varepsilon}$$
for all sufficiently large $N$.

The lower bound $N^{1/4} \ll F(N)$ is due to Bosznay [Bo89], and the upper bound
$F(N) \ll N^{1/4+o(1)}$ is due to Pham and Zakharov [PhZa24].
-/
@[category research solved, AMS 5 11]
theorem erdos_186 :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop,
        (N : ℝ) ^ ((1 : ℝ) / 4 - ε) ≤ (nonAvgMax N : ℝ) ∧
        (nonAvgMax N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4 + ε) := by
  sorry

end Erdos186
