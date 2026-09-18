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
# Number of $0 < k < n$ such that $\pi(kn)$ is prime

Let $\pi$ denote the prime counting function. The sequence $a(n)$ counts the number of integers
$0 < k < n$ such that $\pi(kn)$ is prime.

*References:*
- [A237578](https://oeis.org/A237578)
-/

namespace OeisA237578

/-- $a(n)$ is the number of integers $0 < k < n$ such that $\pi(k \cdot n)$ is prime. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Ico 1 n,
    if (Nat.primeCounting (k * n)).Prime then 1 else 0

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 2 := by decide

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by decide

/--
Conjecture: $a(n) > 0$ for all $n > 2$.
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : 2 < n) : 0 < a n := by
  sorry

/--
and $a(n) = 1$ only for $n = 5, 8, 13$.
-/
@[category research open, AMS 11]
theorem conjecture2 (n : ℕ) :
    a n = 1 ↔ n = 5 ∨ n = 8 ∨ n = 13 := by
  sorry

/--
Moreover, for each $n = 1, 2, 3, \dots$, there is a positive integer $k < 3\sqrt{n} + 3$ with
$\pi(kn)$ prime.
-/
@[category research open, AMS 11]
theorem conjecture3 (n : ℕ) (hn : 1 ≤ n) :
    ∃ k : ℕ, 0 < k ∧ (k : ℝ) < 3 * Real.sqrt (n : ℝ) + 3 ∧
      (Nat.primeCounting (k * n)).Prime := by
  sorry

end OeisA237578
