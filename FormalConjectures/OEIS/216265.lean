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
# Number of primes between $n^3 - n$ and $n^3$

For $n \ge 1$, $a(n)$ is the number of primes $p$ satisfying $n^3 - n < p \le n^3$,
given by $\pi(n^3) - \pi(n^3 - n)$.

*References:*
- [A216265](https://oeis.org/A216265)
-/

namespace OeisA216265

/-- `a n` is the number of primes between $n^3 - n$ and $n^3$. -/
def a (n : ℕ) : ℕ :=
  Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by native_decide

@[category test, AMS 11]
theorem a_5 : a 5 = 0 := by native_decide

/--
Conjecture: For every $n > 13$, $a(n) > 0$.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 13 < n) : 0 < a n := by
  sorry

end OeisA216265
