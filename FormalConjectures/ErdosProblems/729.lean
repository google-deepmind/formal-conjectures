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
import Mathlib.NumberTheory.SmoothNumbers

/-!
# Erdős Problem 729

*Reference:* [erdosproblems.com/729](https://www.erdosproblems.com/729)

Erdős proved that if $a! b! \mid n!$ then $a + b \le n + O(\log n)$. This problem asks
whether the same bound holds when divisibility is only required "up to small
primes," i.e., the denominator of $n!/(a! b!)$ is supported only on bounded primes.

The answer is yes (the bound still holds). Proved by Barreto and Leeham.

[Er68c] Erdős, P., _Aufgabe 557_. Elemente Math. (1968), 111–113.
-/

namespace Erdos729

/--
Erdős Problem 729 [Er68c]:

For any $C > 0$ and any prime bound $P$, the set of triples $(a, b, n)$ such that
$a + b > n + C \cdot \log n$ and the denominator of $n!/(a! b!)$ is $P$-smooth, is finite.
-/
@[category research solved, AMS 11]
theorem erdos_729 : answer(True) ↔
    ∀ (C : ℝ), C > 0 → ∀ (P : ℕ), Set.Finite {t : ℕ × ℕ × ℕ |
      (t.1 : ℝ) + (t.2.1 : ℝ) > (t.2.2 : ℝ) + C * Real.log (t.2.2 : ℝ) ∧
      ((t.2.2.factorial : ℚ) / ((t.1.factorial : ℚ) * (t.2.1.factorial : ℚ))).den ∈
        Nat.smoothNumbers (P + 1)} := by
  sorry

end Erdos729
