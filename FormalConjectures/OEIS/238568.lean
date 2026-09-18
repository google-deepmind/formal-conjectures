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
# Number of positive integers $k < n$ such that $n^2 - \pi(k n)$ is prime

The sequence $a(n)$ counts the number of positive integers $k < n$ such that
$n^2 - \pi(k n)$ is prime, where $\pi(x)$ is the prime counting function:
$$a(n) = |\{0 < k < n : n^2 - \pi(k n) \text{ is prime}\}|$$

*References:*
- [A238568](https://oeis.org/A238568)
- [Problems on combinatorial properties of primes](https://arxiv.org/abs/1402.6641)
  by *Zhi-Wei Sun* (2014)
-/

namespace OeisA238568

open Finset

/-- Number of positive integers $k < n$ such that $n^2 - \pi(k n)$ is prime. -/
def a (n : ℕ) : ℕ :=
  ((Ico 1 n).filter fun k => Nat.Prime (n ^ 2 - Nat.primeCounting (k * n))).card

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
Conjecture (i): $a(n) > 0$ for all $n > 1$, and $a(n) = 1$ only for
$n \in \{2, 3, 4, 8, 10, 24, 41\}$.
-/
@[category research open, AMS 11]
theorem conjecture1 :
    (∀ n : ℕ, 1 < n → 0 < a n) ∧
    (∀ n : ℕ, a n = 1 ↔ n ∈ ({2, 3, 4, 8, 10, 24, 41} : Set ℕ)) := by
  sorry

/--
Conjecture (ii): For any integer $n > 6$, there is a positive integer $k < n$ with
$n^2 + \pi(k n) - 1$ prime.
-/
@[category research open, AMS 11]
theorem conjecture2 (n : ℕ) (hn : 6 < n) :
    ∃ k : ℕ, 0 < k ∧ k < n ∧ Nat.Prime (n ^ 2 + Nat.primeCounting (k * n) - 1) := by
  sorry

/--
Conjecture (iii), part 1: If $n > 2$, then $\pi(n^2) - \pi(k n)$ is prime for some $0 < k < n$.
-/
@[category research open, AMS 11]
theorem conjecture3 (n : ℕ) (hn : 2 < n) :
    ∃ k : ℕ, 0 < k ∧ k < n ∧
      Nat.Prime (Nat.primeCounting (n ^ 2) - Nat.primeCounting (k * n)) := by
  sorry

/--
Conjecture (iii), part 2: If $n > 1$, then $\pi(n^2) + \pi(k n) - 1$ is prime for some $0 < k < n$.
-/
@[category research open, AMS 11]
theorem conjecture4 (n : ℕ) (hn : 1 < n) :
    ∃ k : ℕ, 0 < k ∧ k < n ∧
      Nat.Prime (Nat.primeCounting (n ^ 2) + Nat.primeCounting (k * n) - 1) := by
  sorry

end OeisA238568
