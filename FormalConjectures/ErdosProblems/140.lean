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
# Erdős Problem 140

*Reference:* [erdosproblems.com/140](https://www.erdosproblems.com/140)

Let $r_3(N)$ denote the size of the largest subset of $\{1, \ldots, N\}$ that contains no
non-trivial $3$-term arithmetic progression. Is it true that $r_3(N) \ll N / (\log N)^C$ for
every $C > 0$?

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).

[Er81] Erdős, P., *Problems and results in combinatorial number theory* (1981).

[Er97c] Erdős, P. (1997).

[KeMe23] Kelley, Z. and Meka, R., *Strong bounds for 3-progressions* (2023).
-/

open Real Filter

namespace Erdos140

/-- A finite set $S \subseteq \mathbb{N}$ is $3$-AP-free if it contains no non-trivial $3$-term
arithmetic progression: for all $a, b, c \in S$ satisfying $a + c = 2b$,
we have $a = b$ (which forces $a = b = c$, i.e., the progression is trivial). -/
def IsThreeAPFree (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a + c = 2 * b → a = b

/-- $r_3(N)$ is the maximum size of a $3$-AP-free subset of $\{1, \ldots, N\}$. -/
noncomputable def r3 (N : ℕ) : ℕ :=
  sSup { k : ℕ | ∃ S : Finset ℕ,
    (∀ x ∈ S, 1 ≤ x ∧ x ≤ N) ∧
    IsThreeAPFree S ∧
    S.card = k }

/--
Erdős Problem 140 [ErGr80, Er81, Er97c]:
Let $r_3(N)$ be the size of the largest subset of $\{1, \ldots, N\}$ containing no
non-trivial $3$-term arithmetic progression. Then $r_3(N) \ll N / (\log N)^C$
for every $C > 0$.

Formally: for every $C > 0$ there exists a constant $K > 0$ such that
$$r_3(N) \leq K \cdot N / (\log N)^C$$
for all sufficiently large $N$.

Proved by Kelley and Meka [KeMe23].
-/
@[category research solved, AMS 5 11]
theorem erdos_140 :
    ∀ C : ℝ, 0 < C →
    ∃ K : ℝ, 0 < K ∧
    ∀ᶠ N : ℕ in atTop,
      (r3 N : ℝ) ≤ K * (N : ℝ) / (Real.log (N : ℝ)) ^ C := by
  sorry

end Erdos140
