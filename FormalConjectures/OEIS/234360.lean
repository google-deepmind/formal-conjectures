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
# Number of integers $0 < k < n$ such that $(k + 1)^{\phi(n - k)} + k$ is prime

*References:*
- [A234360](https://oeis.org/A234360)
-/

namespace OeisA234360

/--
The primary defining sequence `a`.
$a(n)$ is the number of integers $0 < k < n$ such that $(k + 1)^{\phi(n - k)} + k$ is prime,
where $\phi$ is Euler's totient function.
-/
def a (n : ℕ) : ℕ :=
  (Finset.filter (fun k =>
    Nat.Prime ((k + 1) ^ (n - k).totient + k)
  ) (Finset.Ico 1 n)).card

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 3 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 3 := by decide

/--
Conjecture (i): $a(n) > 0$ for all $n > 1$.
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : 1 < n) : 0 < a n := by
  sorry

/--
Conjecture (i): For any $n > 5$ there is a positive integer $k < n$ with
$(k + 1)^{\phi(n - k) / 2} - k$ prime.
-/
@[category research open, AMS 11]
theorem conjecture2 (n : ℕ) (hn : 5 < n) :
    ∃ k, 0 < k ∧ k < n ∧ Nat.Prime ((k + 1) ^ ((n - k).totient / 2) - k) := by
  sorry

/--
Conjecture (ii): If $n > 1$, then $k(k + 1)^{\phi(n - k)} + 1$ is prime for some $0 < k < n$.
-/
@[category research open, AMS 11]
theorem conjecture3 (n : ℕ) (hn : 1 < n) :
    ∃ k, 0 < k ∧ k < n ∧ Nat.Prime (k * (k + 1) ^ (n - k).totient + 1) := by
  sorry

/--
Conjecture (ii): If $n > 3$, then $k(k + 1)^{\phi(n - k) / 2} - 1$ is prime for some $0 < k < n$.
-/
@[category research open, AMS 11]
theorem conjecture4 (n : ℕ) (hn : 3 < n) :
    ∃ k, 0 < k ∧ k < n ∧ Nat.Prime (k * (k + 1) ^ ((n - k).totient / 2) - 1) := by
  sorry

end OeisA234360
