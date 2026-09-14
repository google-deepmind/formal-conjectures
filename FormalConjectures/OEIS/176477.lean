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

import FormalConjecturesUtil

/-!
# Recurrence with fourth powers of binomial coefficients

The sequence is defined by $a(1) = 2$, and for $n \ge 2$,
$$(2n+1)^3 a(n) = 32n^3 a(n-1) + (21n^3 + 22n^2 + 8n + 1) \binom{2n-1}{n}^4.$$

*References:*
- [A176477](https://oeis.org/A176477)
- Z.-W. Sun, "Open Conjectures on Congruences", arXiv preprint
  [arXiv:0911.5665](https://arxiv.org/abs/0911.5665) [math.NT], 2009-2011.-/

namespace OeisA176477

/-- Rational recurrence sequence $a(n)$. -/
def a : ℕ → ℚ
  | 0 => 0
  | 1 => 2
  | n + 2 =>
    let idx : ℚ := n + 2
    let prev := a (n + 1)
    (32 * idx ^ 3 * prev +
      (21 * idx ^ 3 + 22 * idx ^ 2 + 8 * idx + 1) *
        ((2 * (n + 2) - 1).choose (n + 2) : ℚ) ^ 4) /
      (2 * idx + 1) ^ 3

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by rfl

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 181 := by decide +native

/--
Each term $a(n)$ is a positive integer.
- _Zhi-Wei Sun_, Apr 06 2010
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : 1 ≤ n) : (a n).den = 1 ∧ 0 < a n := by
  sorry

/--
$a(n)$ is odd if and only if $n = 2, 2^2, 2^3, \dots$.
- _Zhi-Wei Sun_, Apr 06 2010
-/
@[category research open, AMS 11]
theorem conjecture2 (n : ℕ) (hn : 1 ≤ n) :
    ((a n).den = 1 ∧ Odd (a n).num) ↔ ∃ m : ℕ, 1 ≤ m ∧ n = 2 ^ m := by
  sorry

end OeisA176477

