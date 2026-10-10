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
# Sequence designed to show there are infinitely many primes congruent to $1$ modulo $4$

The sequence defined by $a(0) = 1$, $a(1) = 5$, and for $n > 1$,
$a(n) = (a(n-1) - 1) \cdot a(n-1)^2 + 1 = 1 + 4 \prod_{i=1}^{n-1} a(i)^2$.

*References:*
- [A231830](https://oeis.org/A231830)
-/

namespace OeisA231830

/-- The sequence defined by $a(0) = 1$, $a(1) = 5$, and for $n > 1$,
$a(n) = (a(n-1) - 1) \cdot a(n-1)^2 + 1$. -/
def a : ℕ → ℕ
  | 0 => 1
  | 1 => 5
  | n + 2 => (a (n + 1) - 1) * (a (n + 1)) ^ 2 + 1

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 5 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 101 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 1020101 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 1061522231810040101 := by rfl

/--
Similarly to Sylvester's sequence (A000058), it is unknown if all terms are squarefree.
-/
@[category research open, AMS 11]
theorem conjecture :
    answer(sorry) ↔ ∀ n : ℕ, Squarefree (a n) := by
  sorry

end OeisA231830
