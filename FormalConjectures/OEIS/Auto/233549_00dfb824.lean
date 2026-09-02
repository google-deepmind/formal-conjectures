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

import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A233549: Number of ways to write $n = p + q$ ($q > 0$) with $p$ prime and $(\phi(p)\phi(q))^4 + 1$ prime,
where $\phi(\cdot)$ is Euler's totient function (A000010).
-/
def a (n : ℕ) : ℕ :=
  Finset.card <| Finset.filter (fun p : ℕ =>
    p.Prime ∧
    let q := n - p
    Nat.Prime ((p.totient * q.totient) ^ 4 + 1)
  ) (Finset.range n)


theorem a_one : a 1 = 0 := by sorry

theorem a_two : a 2 = 0 := by sorry

theorem a_three : a 3 = 1 := by sorry

theorem a_four : a 4 = 2 := by sorry


/--
Conjecture: (i) a(n) > 0 for all n > 2.
Part (i) of the conjecture implies that there are infinitely many primes of the form x^4 + 1.
-/
theorem oeis_233549_conjecture_1 :
  (∀ n, 2 < n → 0 < a n) →
  Set.Infinite {p : ℕ | Nat.Prime p ∧ ∃ x : ℕ, p = x ^ 4 + 1} :=
by sorry
