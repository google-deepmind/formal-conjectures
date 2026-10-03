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
# Sum of $d \cdot \tau(d)$ over proper divisors $d$ of $n$

The sequence $a(n)$ is the sum of $d \cdot \tau(d)$ over all proper divisors $d < n$ of $n$,
where $\tau(d)$ is the number of divisors of $d$:
$$a(n) = \sum_{d \mid n, d < n} d \cdot \tau(d)$$

*References:*
- [A245211](https://oeis.org/A245211)
-/

namespace OeisA245211

open Finset

/-- Sum over all proper divisors $d$ of $n$ of $d \cdot \tau(d)$, where $\tau(d)$ is the
number of divisors of $d$. -/
def a (n : ℕ) : ℕ :=
  ∑ d ∈ n.properDivisors, d * d.divisors.card

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
theorem a_4 : a 4 = 5 := by
  decide

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by
  decide

/--
Conjecture: $21$ is the only positive integer $n$ such that $a(n) = n$.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 0 < n) : a n = n ↔ n = 21 := by
  sorry

end OeisA245211
