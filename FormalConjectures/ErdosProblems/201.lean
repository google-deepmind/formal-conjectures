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
# Erdős Problem 201

*Reference:* [erdosproblems.com/201](https://www.erdosproblems.com/201)

Let $G_k(N)$ be such that any set of $N$ integers contains a subset of
size at least $G_k(N)$ which does not contain a $k$-term arithmetic
progression. Let $R_k(N)$ be the size of the largest subset of
$\{1,\ldots,N\}$ without a $k$-term arithmetic progression.

It is trivial that $G_k(N) \leq R_k(N)$. Komlós, Sulyok, and Szemerédi
[KSS75] showed that $R_k(N) \ll_k G_k(N)$.

[Er73] Erdős, P., *Problems and results on combinatorial number theory*. A survey of
combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo.,
1971) (1973), 117-138.

[Er75b] Erdős, P., *Problems and results on combinatorial number theory III*. Number Theory Day
(Proc. Conf., Rockefeller Univ., New York, 1976) (1975).

[ErGr79] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory I*. Enseign. Math. (1979).

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).

[KSS75] Komlós, J., Sulyok, M. and Szemerédi, E., *Linear problems in combinatorial number
theory*. Acta Math. Acad. Sci. Hungar. (1975).
-/

open Classical

namespace Erdos201

/--
A finset of integers contains a $k$-term arithmetic progression if there
exist integers $a$, $d$ with $d \neq 0$ such that $a + i \cdot d \in S$ for all
$0 \leq i < k$.
-/
def HasKTermAP (k : ℕ) (S : Finset ℤ) : Prop :=
  ∃ a d : ℤ, d ≠ 0 ∧ ∀ i : Fin k, (a + (i.val : ℤ) * d) ∈ S

/-- The maximum cardinality of a subset of $S$ that contains no $k$-term AP. -/
noncomputable def maxAPFreeSize (k : ℕ) (S : Finset ℤ) : ℕ :=
  Finset.sup (S.powerset.filter (fun T => ¬HasKTermAP k T)) Finset.card

/-- $R_k(N)$: the size of the largest subset of $\{1, \ldots, N\}$ without a $k$-term AP. -/
noncomputable def rAp (k N : ℕ) : ℕ :=
  maxAPFreeSize k (Finset.Icc (1 : ℤ) (N : ℤ))

/--
Erdős Problem #201 [Er73, Er75b, ErGr79, ErGr80]:

Is it true that $\lim_{N \to \infty} R_3(N) / G_3(N) = 1$?

Since $G_k(N) \leq R_k(N)$ always holds, the conjecture is equivalent to:
for every $\varepsilon > 0$, for all sufficiently large $N$, every set of $N$ integers
contains a $3$-AP-free subset of size at least $(1 - \varepsilon) \cdot R_3(N)$.
-/
@[category research open, AMS 5]
theorem erdos_201 :
    answer(sorry) ↔
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ S : Finset ℤ, S.card = N →
        ∃ T ⊆ S, ¬HasKTermAP 3 T ∧
          (1 - ε) * (rAp 3 N : ℝ) ≤ (T.card : ℝ) := by
  sorry

end Erdos201
