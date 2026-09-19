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
# Number of integers $0 < k \le n$ such that $\pi(\pi(k n))$ is a square

The sequence $a(n)$ counts the number of integers $k \in \{1, \dots, n\}$ such that
$\pi(\pi(k n))$ is a square, where $\pi(x)$ is the prime counting function:
$$a(n) = |\{0 < k \le n : \pi(\pi(k n)) \text{ is a square}\}|$$

*References:*
- [A238902](https://oeis.org/A238902)
- [Problems on combinatorial properties of primes](https://arxiv.org/abs/1402.6641)
  by *Zhi-Wei Sun* (2014)
-/

namespace OeisA238902

open Finset

/-- Number of integers $0 < k \le n$ such that $\pi(\pi(k n))$ is a square. -/
def a (n : ℕ) : ℕ :=
  ((Icc 1 n).filter fun k =>
    let m := Nat.primeCounting (Nat.primeCounting (k * n))
    m.sqrt ^ 2 = m).card

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by
  decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by
  native_decide

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by
  native_decide

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 2 := by
  native_decide

/--
Conjecture (i): $a(n) > 0$ for all $n > 0$.
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : 0 < n) : 0 < a n := by
  sorry

/--
Conjecture (ii): For every $n = 1, 2, 3, \dots$, there exists a positive integer
$k \le (n + 1) / 2$ such that $\pi(\pi(k n))$ is a triangular number.
-/
@[category research open, AMS 11]
theorem conjecture2 (n : ℕ) (hn : 0 < n) :
    ∃ k : ℕ, 0 < k ∧ k ≤ (n + 1) / 2 ∧
      ∃ m : ℕ, Nat.primeCounting (Nat.primeCounting (k * n)) = m * (m + 1) / 2 := by
  sorry

end OeisA238902
