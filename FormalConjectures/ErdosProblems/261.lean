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
# Erdős Problem 261

*Reference:* [erdosproblems.com/261](https://www.erdosproblems.com/261)

[Er74b] Erdős, P., *Problems and results on combinatorial number theory III*.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial
number theory*.

[Er88c] Erdős, P., *Problems and results on combinatorial number theory*.

[BoLo90] Borwein, D. and Loring, T., *Some questions of Erdős and Graham on numbers
of the form $\sum g_n / 2^{g_n}$*.
-/

open scoped BigOperators

namespace Erdos261

/-- A positive integer $n$ has the Erdős-261 property if $n/2^n$ can be written as
a finite sum $\sum_{a \in S} a/2^a$ for some set $S$ of at least 2 distinct positive
integers. -/
noncomputable def HasErdos261Property (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, 2 ≤ S.card ∧ (∀ a ∈ S, 0 < a) ∧
    (n : ℝ) / (2 : ℝ) ^ n = ∑ a ∈ S, (a : ℝ) / (2 : ℝ) ^ a

/--
Erdős Problem 261 [Er74b, ErGr80, Er88c]:
Is it true for all positive integers $n$ that $n/2^n$ can be written as a finite
sum of at least 2 distinct terms $a/2^a$?
-/
@[category research open, AMS 11]
theorem erdos_261 : answer(sorry) ↔ ∀ n : ℕ, 0 < n → HasErdos261Property n := by
  sorry

/--
Erdős Problem 261, weaker variant [Er74b, ErGr80, Er88c]:
Are there infinitely many $n$ such that there exists some $t \geq 2$ and distinct
integers $a_1, \ldots, a_t \geq 1$ such that $n/2^n = \sum_{k \leq t} a_k/2^{a_k}$?

This was proved by Cusick; Borwein and Loring [BoLo90] showed that for
$n = 2^{m+1} - m - 2$, the representation holds for every positive integer $m$.
-/
@[category research solved, AMS 11]
theorem erdos_261.variants.infinitely_many :
    Set.Infinite {n : ℕ | HasErdos261Property n} := by
  sorry

/--
Erdős Problem 261, uncountable representations variant [Er74b, ErGr80, Er88c]:
Is there a rational $x$ such that $x = \sum_{k=1}^{\infty} a_k/2^{a_k}$ has at least
$2^{\aleph_0}$ solutions, where the $a_k$ form a strictly increasing sequence of
positive integers?
-/
@[category research open, AMS 11]
theorem erdos_261.variants.uncountable_representations :
    answer(sorry) ↔ ∃ x : ℝ, (∃ q : ℚ, x = (q : ℝ)) ∧
      ¬ Set.Countable {a : ℕ → ℕ | StrictMono a ∧ (∀ n, 0 < a n) ∧
        HasSum (fun n => (a n : ℝ) / (2 : ℝ) ^ (a n)) x} := by
  sorry

end Erdos261
