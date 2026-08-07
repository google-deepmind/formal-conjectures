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

open Nat Finset ArithmeticFunction

/--
A233544: Number of ways to write $n = k^2 + m$ with $k > 0$ and $m \ge k^2$ such that
$\sigma(k^2) + \phi(m)$ is prime, where $\sigma(k^2)$ is the sum of all (positive) divisors of $k^2$,
and $\phi(\cdot)$ is Euler's totient function (A000010).
-/
def a (n : ℕ) : ℕ :=
  let max_k : ℕ := Nat.sqrt (n / 2)
  Finset.sum (Finset.Icc 1 max_k) fun k =>
    let m := n - k ^ 2
    if (sigma 1 (k ^ 2) + m.totient).Prime then 1 else 0


/-- A233544 Conjecture (i): $a(n) > 0$ for all $n > 1$.
I verified the conjecture to 3*10^9. The conjecture is almost surely true.
Part (i) of the conjecture is stronger than the conjecture in A232270.
There are no counterexamples to conjecture (i) < 5.12 * 10^10.
-/
theorem A233544_conjecture_i : ∀ (n : ℕ), n > 1 → a n > 0 :=
  by sorry
