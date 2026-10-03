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
# Number of primes $p \le (n+1)/2$ with $\lfloor\sqrt{n-p}\rfloor$ prime

The sequence $a(n)$ counts the number of primes $p \le \lfloor (n+1)/2 \rfloor$ such that
$\lfloor\sqrt{n-p}\rfloor$ is prime.

*References:*
- [A237720](https://oeis.org/A237720)
-/

namespace OeisA237720

/-- $a(n)$ is the number of primes $p \le \lfloor (n+1)/2 \rfloor$ with $\lfloor\sqrt{n-p}\rfloor$
prime. -/
def a (n : ℕ) : ℕ :=
  ∑ p ∈ Finset.Icc 1 ((n + 1) / 2),
    if p.Prime ∧ (Nat.sqrt (n - p)).Prime then 1 else 0

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide +native

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by decide +native

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by decide +native

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
Conjecture (i): $a(n) > 0$ for all $n > 5$.
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : 5 < n) : 0 < a n := by
  sorry

/--
Conjecture: $a(n) = 1$ only for $n = 6, 23, 24, 111, 112, \ldots, 120$.
-/
@[category research open, AMS 11]
theorem conjecture2 (n : ℕ) :
    a n = 1 ↔ n = 6 ∨ n = 23 ∨ n = 24 ∨ (111 ≤ n ∧ n ≤ 120) := by
  sorry

/--
Conjecture (ii): For any integer $n > 2$, there is a prime $p < n$
with $\lfloor\sqrt{n+p}\rfloor$ prime.
-/
@[category research open, AMS 11]
theorem conjecture3 (n : ℕ) (hn : 2 < n) :
    ∃ p : ℕ, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  sorry

end OeisA237720
