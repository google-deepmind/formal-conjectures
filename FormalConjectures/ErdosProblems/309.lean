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
# Erdős Problem 309

*Reference:* [erdosproblems.com/309](https://www.erdosproblems.com/309)

Let $F(N)$ count the number of positive integers representable as sums of distinct unit fractions
with denominators from $\{1, \ldots, N\}$. Erdős conjectured that $F(N) = o(\log N)$. This was
disproved by Yokota, who showed $F(N) = \Theta(\log N)$.

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial
number theory_. Monographies de L'Enseignement Mathematique (1980).

[Yo97] Yokota, H., _On number of integers representable as a sum of unit fractions. II_.
J. Number Theory (1997), 162-169.

[Cr99] Croot III, E. S., _On some questions of Erdős and Graham about Egyptian fractions_.
Mathematika (1999), 359-372.

[Yo02] Yokota, H., _On the number of integers representable as sums of unit fractions. III_.
J. Number Theory (2002), 351-372.

See also OEIS A217693.
-/

open Classical Filter

open scoped BigOperators

namespace Erdos309

/--
A positive integer $k$ is representable as a sum of distinct unit fractions with
denominators from $\{1, \ldots, N\}$ if there exists a subset $S \subseteq \{1, \ldots, N\}$ such
that $\sum_{n \in S} 1/n = k$.
-/
def IsRepresentableUnitFractionSum (N : ℕ) (k : ℕ) : Prop :=
  ∃ S : Finset ℕ, (∀ n ∈ S, 1 ≤ n ∧ n ≤ N) ∧
    ∑ n ∈ S, (1 : ℚ) / (n : ℚ) = (k : ℚ)

/--
$F(N)$ counts the number of positive integers that can be represented as sums of distinct
unit fractions with denominators from $\{1, \ldots, N\}$.
-/
noncomputable def countRepresentableIntegers (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter (fun k => 0 < k ∧ IsRepresentableUnitFractionSum N k)).card

/--
Erdős Problem 309 (disproved) [ErGr80]:

Let $N \geq 1$. How many integers can be written as the sum of distinct unit fractions
with denominators from $\{1, \ldots, N\}$? Erdős conjectured that there are $o(\log N)$ such
integers. This was disproved.

The trivial upper bound is $F(N) \leq \log N + O(1)$. Yokota [Yo97] proved that
$F(N) \geq \log N - O(\log \log N)$, establishing that $F(N) = \Theta(\log N)$.

We formalize the negation of the original conjecture: there exists a positive
constant $c$ such that $F(N) \geq c \cdot \log N$ for all sufficiently large $N$.
-/
@[category research solved, AMS 11]
theorem erdos_309 :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ (N : ℕ) in atTop,
      c * Real.log (N : ℝ) ≤ (countRepresentableIntegers N : ℝ) := by
  sorry

/--
Trivial upper bound for $F(N)$: the number of representable integers is at most $\log N + O(1)$,
since the full harmonic sum $\sum_{n=1}^{N} 1/n = \log N + \gamma + O(1/N)$ bounds the largest
representable integer.
-/
@[category research solved, AMS 11]
theorem erdos_309_upper :
    ∃ C : ℝ, ∀ᶠ (N : ℕ) in atTop,
      (countRepresentableIntegers N : ℝ) ≤ Real.log (N : ℝ) + C := by
  sorry

/--
Yokota's refined lower bound [Yo02]: $F(N) \geq \log N + \gamma -
(\pi^2/3 + o(1))(\log \log N)^2 / \log N$, where $\gamma$ is the Euler–Mascheroni constant.
This is the current best lower bound and establishes $F(N) = \Theta(\log N)$ together with the
trivial upper bound.
-/
@[category research solved, AMS 11]
theorem erdos_309_yokota_lower :
    ∀ ε > 0, ∀ᶠ (N : ℕ) in atTop,
      Real.log (N : ℝ) + Real.eulerMascheroniConstant -
        (Real.pi ^ 2 / 3 + ε) * (Real.log (Real.log (N : ℝ))) ^ 2 / Real.log (N : ℝ)
      ≤ (countRepresentableIntegers N : ℝ) := by
  sorry

end Erdos309
