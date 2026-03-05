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
# Erdős Problem 308

*Reference:* [erdosproblems.com/308](https://www.erdosproblems.com/308)

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial
number theory*. Monographies de L'Enseignement Mathematique (1980).

[Cr99] Croot, E., *On unit fractions*. Ph.D. thesis, University of Georgia (1999).
-/

open Finset

open scoped BigOperators

namespace Erdos308

/--
A positive integer $k$ is representable as a sum of distinct unit fractions with
denominators from $\{1, \ldots, N\}$ if there exists a subset $S \subseteq \{1, \ldots, N\}$
such that $\sum_{n \in S} 1/n = k$.
-/
def IsRepresentableUnitFractionSum (N : ℕ) (k : ℕ) : Prop :=
  ∃ S : Finset ℕ, (∀ n ∈ S, 1 ≤ n ∧ n ≤ N) ∧
    ∑ n ∈ S, (1 : ℚ) / (n : ℚ) = (k : ℚ)

/--
Erdős Problem 308 [ErGr80]:

Is it true that for every $N \geq 1$, the set of positive integers representable as sums of
distinct unit fractions with denominators from $\{1, \ldots, N\}$ has the shape
$\{1, \ldots, m\}$ for some $m$?

This was essentially solved by Croot [Cr99], who showed that if $f(N)$ is the smallest
positive integer not so representable, and $m_N = \lfloor \sum_{n \leq N} 1/n \rfloor$, then
for all sufficiently large $N$ the set of representable positive integers is either
$\{1, \ldots, m_N - 1\}$ or $\{1, \ldots, m_N\}$.
-/
@[category research solved, AMS 11]
theorem erdos_308 : answer(True) ↔ ∀ N : ℕ, 1 ≤ N →
    ∃ m : ℕ, (∀ k : ℕ, 1 ≤ k → k ≤ m → IsRepresentableUnitFractionSum N k) ∧
      (∀ k : ℕ, m < k → ¬ IsRepresentableUnitFractionSum N k) := by
  sorry

end Erdos308
