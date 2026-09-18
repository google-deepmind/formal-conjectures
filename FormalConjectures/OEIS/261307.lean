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
# Prime values in recurrence $a(n+1) = |a(n) - \gcd(a(n), 7n+6)|$

Let $a(1) = 1$ and $a(n+1) = |a(n) - \gcd(a(n), 7n+6)|$ for $n \ge 1$.
It is conjectured that whenever $a(n) = 0$ for $n > 2$, the value $7n+6 = a(n+1)$ is prime.

*References:*
- [A261307](https://oeis.org/A261307)
-/

namespace OeisA261307

/--
The sequence $a(n)$ defined by $a(1) = 1$ and $a(n+1) = |a(n) - \gcd(a(n), 7n+6)|$.
For $n = 0$, $a(0)$ is set to $0$.
-/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    let prev := a (n + 1)
    Int.natAbs ((prev : ℤ) - (Nat.gcd prev (7 * (n + 1) + 6) : ℤ))

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 20 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 19 := by rfl

@[category test, AMS 11]
theorem a_5 : a 5 = 18 := by rfl

/--
It is conjectured that for all $n > 2$, $a(n) = 0$ implies that $7n+6 = a(n+1)$ is prime,
cf. A186259.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 2 < n) (ha : a n = 0) : Nat.Prime (7 * n + 6) := by
  sorry

end OeisA261307
