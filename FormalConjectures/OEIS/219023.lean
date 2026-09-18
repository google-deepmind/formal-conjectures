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
# Primes $p < n$ with $n^2 - n + p$ and $n^2 + n - p$ prime

For $n \ge 1$, $a(n)$ is the number of primes $p < n$ such that $n^2 - n + p$ and $n^2 + n - p$
are both prime.

*References:*
- [A219023](https://oeis.org/A219023)
-/

namespace OeisA219023

/-- $a(n)$ is the number of primes $p < n$ such that $n^2 - n + p$ and $n^2 + n - p$
are both prime. -/
def a (n : ℕ) : ℕ :=
  ∑ p ∈ (Finset.range n).filter Nat.Prime,
    if Nat.Prime (n ^ 2 - n + p) ∧ Nat.Prime (n ^ 2 + n - p) then 1 else 0

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 0 := by decide

@[category test, AMS 11]
theorem a_8 : a 8 = 1 := by decide

/--
Conjecture: $a(n) > 0$ for all $n > 2732$.
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : 2732 < n) : 0 < a n := by
  sorry

/--
Conjecture: For $n > 3512$, there is a prime $p \in (n, 2n)$
such that both $n^2 - n + p$ and $n^2 + n - p$ are prime.
- Zhi-Wei Sun
-/
@[category research open, AMS 11]
theorem conjecture2 (n : ℕ) (hn : 3512 < n) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p < 2 * n ∧
      Nat.Prime (n ^ 2 - n + p) ∧ Nat.Prime (n ^ 2 + n - p) := by
  sorry

/--
Conjecture: For $n > 1828$, there is a prime $p < n$ such that
both $n^2 - n - p$ and $n^2 + n + p$ are prime.
- Zhi-Wei Sun
-/
@[category research open, AMS 11]
theorem conjecture3 (n : ℕ) (hn : 1828 < n) :
    ∃ p : ℕ, p.Prime ∧ p < n ∧
      Nat.Prime (n ^ 2 - n - p) ∧ Nat.Prime (n ^ 2 + n + p) := by
  sorry

/--
Conjecture: For $n > 4517$, there is a prime $p \in (n, 2n)$
such that both $n^2 - n - p$ and $n^2 + n + p$ are prime.
- Zhi-Wei Sun
-/
@[category research open, AMS 11]
theorem conjecture4 (n : ℕ) (hn : 4517 < n) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p < 2 * n ∧
      Nat.Prime (n ^ 2 - n - p) ∧ Nat.Prime (n ^ 2 + n + p) := by
  sorry

end OeisA219023
