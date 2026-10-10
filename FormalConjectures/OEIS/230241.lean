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
# Partitions $n = p + q$ with $p$, $3p - 10$, and $(p - 1)q - 1$ prime

Number of ways to write $n = p + q$ with $p$, $3p - 10$ and $(p-1)q - 1$ all prime, where $q$ is a
positive integer.

*References:*
- [A230241](https://oeis.org/A230241)
-/

namespace OeisA230241

/-- Number of ways to write $n = p + q$ with $p$, $3p - 10$ and $(p-1)q - 1$ all prime, where $q$
is a positive integer. -/
def a (n : ℕ) : ℕ :=
  ∑ p ∈ Finset.Ico 1 n,
    if p.Prime ∧ (3 * p - 10).Prime ∧ ((p - 1) * (n - p) - 1).Prime then 1 else 0

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 0 := by rfl

@[category test, AMS 11]
theorem a_5 : a 5 = 0 := by rfl

@[category test, AMS 11]
theorem a_6 : a 6 = 1 := by rfl

/--
Conjecture: $a(n) > 0$ for all $n > 5$.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : n > 5) : a n > 0 := by
  sorry

end OeisA230241
