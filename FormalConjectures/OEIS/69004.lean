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
# Number of times $n^2 + s^2$ is prime for positive integers $s < n$

The sequence $a(n)$ counts the number of integers $s \in \{1, \dots, n-1\}$ such that
$n^2 + s^2$ is prime:
$$a(n) = \sum_{s=1}^{n-1} [\text{Prime}(n^2 + s^2)]$$

*References:*
- [A069004](https://oeis.org/A069004)-/

namespace OeisA69004

open Finset

/-- Number of times $n^2 + s^2$ is prime for positive integers $s < n$. -/
def a (n : ℕ) : ℕ :=
  ∑ s ∈ Ico 1 n, if (n ^ 2 + s ^ 2).Prime then 1 else 0

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by
  decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by
  decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by
  decide

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 2 := by
  decide

/--
Conjecture: $a(n) > 0$ for all $n > 1$.-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : 1 < n) : 0 < a n := by
  sorry

/--
Stronger conjecture: Let $\pi(n)$ be the prime counting function (A000720).
Then $\pi(n) \ge a(n) \ge \pi(n)/5$ for $n > 1$, with the following equalities:
$\pi(2) = a(2)$, $\pi(10) = a(10)$ and $a(12) = \pi(12)/5$.-/
@[category research open, AMS 11]
theorem conjecture2 :
    (∀ n : ℕ, 1 < n → Nat.primeCounting n ≥ a n) ∧
    (∀ n : ℕ, 1 < n → 5 * a n ≥ Nat.primeCounting n) ∧
    Nat.primeCounting 2 = a 2 ∧
    Nat.primeCounting 10 = a 10 ∧
    5 * a 12 = Nat.primeCounting 12 := by
  sorry

end OeisA69004
