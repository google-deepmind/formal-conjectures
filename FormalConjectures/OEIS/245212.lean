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
# Difference between $n \tau(n)$ and $\sum_{d \mid n, d < n} d \tau(d)$

The sequence $a(n) = n \tau(n) - \sum_{d \mid n, d < n} d \tau(d)$, where $\tau(n)$ is the number
of divisors of $n$.

*References:*
- [A245212](https://oeis.org/A245212)
-/

namespace OeisA245212

open Nat Finset

/-- The primary sequence $a(n) = n \tau(n) - \sum_{d \mid n, d < n} d \tau(d)$, where $\tau(n)$
is the number of divisors of $n$. -/
def a (n : ℕ) : ℤ :=
  (n : ℤ) * (n.divisors.card : ℤ) - ∑ d ∈ n.properDivisors, (d : ℤ) * (d.divisors.card : ℤ)

/-- The sum of divisors function $\sigma_1(n)$, cast to $\mathbb{Z}$. -/
def sigma (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, (d : ℤ)

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 5 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 7 := by rfl

@[category test, AMS 11]
theorem a_5 : a 5 = 9 := by rfl

/-- Conjecture: $a(n) = \sigma(n)$ iff $n$ is a power of $2$ (A000079). -/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (h : 0 < n) :
    a n = sigma n ↔ ∃ k : ℕ, n = 2 ^ k := by
  sorry

end OeisA245212
