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
import FormalConjecturesForMathlib.Analysis.HasGaps

/-!
# Erdős Problem 260

Let $a_1 < a_2 < \cdots$ be a strictly increasing sequence of natural numbers with
$a_n / n \to \infty$. Is $\sum a_n / 2^{a_n}$ necessarily irrational?

Erdős proved irrationality under the stronger condition $a_{n+1} - a_n \to \infty$, and also
under $a_n \gg n\sqrt{\log n \log\log n}$. Erdős and Graham speculated that the weaker condition
$\limsup (a_{n+1} - a_n) = \infty$ alone is insufficient, but no counterexample is known.

*Reference:* [erdosproblems.com/260](https://www.erdosproblems.com/260)

[Er74b] Erdős, P., *Problems and results on combinatorial number theory III*.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial
number theory*. Monographies de L'Enseignement Mathematique (1980).

[Er81h] Erdős, P., *Some problems and results in number theory*.

[Er81l] Erdős, P., *Sur l'irrationalité d'une certaine série*. C. R. Acad. Sci. Paris
Sér. I Math. (1981), 765–768.

[Er88c] Erdős, P., *Problems and results on combinatorial number theory*.

[Va99] *Some of Paul's favorite problems*. Booklet for the conference "Paul Erdős and
his mathematics," Budapest (1999), §1.33.
-/

open Filter

namespace Erdos260

/--
Erdős Problem 260 [Er74b, ErGr80, Er81h, Er81l, Er88c, Va99]:
Let $a_1 < a_2 < \cdots$ be a strictly increasing sequence of natural numbers such
that $a_n / n \to \infty$ (i.e., having Fabry gaps). Is $\sum_n a_n / 2^{a_n}$ irrational?
-/
@[category research open, AMS 11]
theorem erdos_260 : answer(sorry) ↔
    ∀ a : ℕ → ℕ,
      HasFabryGaps a →
      Irrational (∑' n, (a n : ℝ) / (2 : ℝ) ^ (a n)) := by
  sorry

/--
Erdős proved that if $a_1 < a_2 < \cdots$ is a strictly increasing sequence of natural
numbers with $a_{n+1} - a_n \to \infty$, then $\sum a_n / 2^{a_n}$ is irrational.
This is a stronger hypothesis than the Fabry gap condition $a_n / n \to \infty$.
-/
@[category research solved, AMS 11]
theorem erdos_260_consecutive_gaps_diverge :
    ∀ a : ℕ → ℕ, StrictMono a →
      Tendsto (fun n => (a (n + 1) : ℝ) - (a n : ℝ)) atTop atTop →
      Irrational (∑' n, (a n : ℝ) / (2 : ℝ) ^ (a n)) := by
  sorry

end Erdos260
