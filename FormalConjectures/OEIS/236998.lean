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
# Number of $0 < k < n/2$ such that $\phi(k)\phi(n-k)$ is a square

Let $\phi$ denote Euler's totient function. The sequence $a(n)$ counts the number of integers
$0 < k < n/2$ such that $\phi(k)\phi(n-k)$ is a square.

*References:*
- [A236998](https://oeis.org/A236998)
-/

namespace OeisA236998

/-- $a(n)$ is the number of integers $0 < k < n/2$ such that $\phi(k)\phi(n-k)$ is a square. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 ((n - 1) / 2),
    if IsSquare (k.totient * (n - k).totient) then 1 else 0

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide +native

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by decide +native

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by decide +native

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 0 := by decide +native

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 0 := by decide +native

/-- Value of the sequence `a` at 6. -/
@[category test, AMS 11]
theorem a_6 : a 6 = 1 := by decide +native

/-- Value of the sequence `a` at 7. -/
@[category test, AMS 11]
theorem a_7 : a 7 = 2 := by decide +native

/--
Conjecture: (i) $a(n) > 0$ for all $n > 8$.
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : 8 < n) : 0 < a n := by
  sorry

/--
Conjecture: (ii) If $n > 20$, then $\phi(k)\phi(n-k) + 1$ is a square for some $0 < k < n/2$.
-/
@[category research open, AMS 11]
theorem conjecture2 (n : ℕ) (hn : 20 < n) :
    ∃ k : ℕ, 0 < k ∧ 2 * k < n ∧ IsSquare (k.totient * (n - k).totient + 1) := by
  sorry

/--
Conjecture: (iii) If $n > 1$ is not among $4, 7, 60, 199, 267$, then $k\phi(n-k)$ is a square for
some $0 < k < n$.
-/
@[category research open, AMS 11]
theorem conjecture3 (n : ℕ) (hn : 1 < n) (h4 : n ≠ 4) (h7 : n ≠ 7) (h60 : n ≠ 60)
    (h199 : n ≠ 199) (h267 : n ≠ 267) :
    ∃ k : ℕ, 0 < k ∧ k < n ∧ IsSquare (k * (n - k).totient) := by
  sorry

end OeisA236998
