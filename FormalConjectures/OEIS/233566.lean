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
# Number of primes $p < n$ such that $p \phi(n - p) - 1$ is also prime

*References:*
- [A233566](https://oeis.org/A233566)
-/

namespace OeisA233566

/--
The primary defining sequence `a`.
$a(n)$ is the number of primes $p < n$ such that $p \phi(n - p) - 1$ is also prime,
where $\phi$ is Euler's totient function.
-/
def a (n : ℕ) : ℕ :=
  Finset.card <| Finset.filter (fun p =>
    p.Prime ∧ Nat.Prime (p * (n - p).totient - 1)
  ) (Finset.range n)

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 2 := by decide

/--
Conjecture: $a(n) > 0$ for all $n > 3$.
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : 3 < n) : 0 < a n := by
  sorry

/--
Conjecture: For any $n > 2$ there is a prime $p < n$ with $p^2 \phi(n - p) - 1$ prime.
-/
@[category research open, AMS 11]
theorem conjecture2 (n : ℕ) (hn : 2 < n) :
    ∃ p < n, p.Prime ∧ Nat.Prime (p ^ 2 * (n - p).totient - 1) := by
  sorry

end OeisA233566
