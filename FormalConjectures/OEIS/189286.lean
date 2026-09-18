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
# Normalized convolution of $\binom{6k}{3k}\binom{3k}{k}$

The sequence $a(n)$ is defined by
$$a(n) = \frac{\sum_{k=0}^n \binom{6k}{3k}\binom{3k}{k}
  \binom{6(n-k)}{3(n-k)}\binom{3(n-k)}{n-k}}{(2n-1)\binom{3n}{n}}.$$

*References:*
- [A189286](https://oeis.org/A189286)
- [OEIS Open](https://arxiv.org/abs/2608.11941)
  by *Tom Adamczewski*, arXiv:2608.11941 (2026)
-/

namespace OeisA189286

/-- The term $\binom{6k}{3k}\binom{3k}{k}$ appearing in the sum. -/
def tTerm (k : ℕ) : ℚ := ((6 * k).choose (3 * k) * (3 * k).choose k : ℕ)

/--
The sequence $a(n)$ given by
$\frac{\sum_{k=0}^n \binom{6k}{3k}\binom{3k}{k}
  \binom{6(n-k)}{3(n-k)}\binom{3(n-k)}{n-k}}{(2n-1)\binom{3n}{n}}$.
-/
def a (n : ℕ) : ℚ :=
  (∑ k ∈ Finset.range (n + 1), tTerm k * tTerm (n - k)) /
    (((2 * (n : ℚ)) - 1) * ((3 * n).choose n : ℚ))

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = -1 := by decide +native

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 40 := by decide +native

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 696 := by decide +native

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 23408 := by decide +native

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 969496 := by decide +native

/--
Conjecture: $a(n)$ is an integer for every $n = 0, 1, 2, \dots$.
- _Zhi-Wei Sun_, Apr 19 2011
-/
@[category research solved, AMS 11]
theorem conjecture1 (n : ℕ) : (a n).den = 1 := by
  sorry

/--
Conjecture (i): $a(n)^{1/n}$ tends to $64$ as $n$ tends to infinity.
- _Zhi-Wei Sun_, Apr 19 2011
-/
@[category research open, AMS 11]
theorem conjecture2 :
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) ^ (1 / (n : ℝ))) Filter.atTop (nhds 64) := by
  sorry

/--
Conjecture (ii): For any positive integer $n$, we have $a(n) \equiv 0 \pmod 8$,
and $a(n)/8$ is odd if and only if $n$ is a power of two.
- _Zhi-Wei Sun_, Apr 19 2011
-/
@[category research open, AMS 11]
theorem conjecture3 (n : ℕ) (hn : 0 < n) :
    ∃ m : ℤ, a n = 8 * m ∧ (Odd m ↔ ∃ k : ℕ, n = 2 ^ k) := by
  sorry

end OeisA189286
