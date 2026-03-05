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
# Erdős Problem 729

*Reference:* [erdosproblems.com/729](https://www.erdosproblems.com/729)

Erdős proved that if $a! b! \mid n!$ then $a + b \le n + O(\log n)$. This problem asks
whether the same bound holds when divisibility is only required "up to small
primes," i.e., the denominator of $n!/(a! b!)$ is supported only on bounded primes.

The answer is yes (the bound still holds). Proved by Barreto and Leeham.

[EGRS75] Erdős, P., Graham, R., Ruzsa, I. Z., and Straus, E. G.,
_On the prime factors of $\binom{2n}{n}$_, Math. Comp. **29** (1975), 83–92.
-/

namespace Erdos729

/-- The denominator of $n!/(a! \cdot b!)$, when written in lowest terms, is $P$-smooth:
all its prime factors are at most $P$. -/
def DenomPSmooth (a b n P : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p →
    p ∣ ((n.factorial : ℚ) / ((a.factorial : ℚ) * (b.factorial : ℚ))).den → p ≤ P

/--
Erdős Problem 729 [EGRS75]:

For any $C > 0$ and any prime bound $P$, the set of triples $(a, b, n)$ such that
$a + b > n + C \cdot \log n$ and the denominator of $n!/(a! b!)$ is $P$-smooth, is finite.
-/
@[category research solved, AMS 11]
theorem erdos_729 : answer(True) ↔
    ∀ (C : ℝ), C > 0 → ∀ (P : ℕ), Set.Finite {t : ℕ × ℕ × ℕ |
      (t.1 : ℝ) + (t.2.1 : ℝ) > (t.2.2 : ℝ) + C * Real.log (t.2.2 : ℝ) ∧
      DenomPSmooth t.1 t.2.1 t.2.2 P} := by
  sorry

end Erdos729
