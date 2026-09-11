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
import FormalConjectures.OEIS.«5153»

/-!
# Denominator of sum of reciprocals of divisors

Denominator of sum of reciprocals of divisors of $n$:
$$\sum_{d \mid n} \frac{1}{d} = \frac{\sigma(n)}{n}$$
in lowest terms.

*References:*
- [A017666](https://oeis.org/A017666)
-/

namespace OeisA17666

/-- Denominator of sum of reciprocals of divisors of $n$. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 1
  else n / Nat.gcd n (∑ d ∈ n.divisors, d)

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by decide

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 3 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 4 := by decide

/--
If $a(n)$ is in A005153, then $n$ is in A005153.
- Jaycob Coleman, Sep 27 2014

We require $0 < n$ because $a(0) = 1$ is in A005153 (practical numbers), but $0$ is not.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 0 < n) : OeisA5153.A (a n) → OeisA5153.A n := by
  sorry

end OeisA17666
