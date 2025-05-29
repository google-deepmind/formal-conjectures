/-
Copyright 2025 The Formal Conjectures Authors.

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
# Collatz conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Collatz_conjecture)
-/
/--
Consider the following operation on the natural numbers:
If the number is even, divide it by two.
If the number is odd, triple it and add one.
-/
def collatzStep (n : ℕ) : ℕ :=
  if Even n then n / 2 else 3 * n + 1

/--
Now form a sequence by performing this operation repeatedly, beginning with any positive integer,
and taking the result at each step as the input at the next.
The **Collatz conjecture** states that for any positive integer $n$, there exists a natural number
$i$ such that the $i$-th term of the sequence is 1.
-/
@[category research open, AMS 11]
theorem CollatzConjecture : ∀ n : ℕ, n > 0 → ∃ m : ℕ, collatzStep^[m] n = 1 := by
  sorry
