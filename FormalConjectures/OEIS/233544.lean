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
# Representations $n = k^2 + m$ ($0 < k^2 \le m$) with $\sigma(k^2) + \phi(m)$ prime

*References:*
- [A233544](https://oeis.org/A233544)
-/

namespace OeisA233544

open ArithmeticFunction

/--
$a(n)$ is the number of ways to write $n = k^2 + m$ with $k > 0$ and $m \ge k^2$ such that
$\sigma(k^2) + \phi(m)$ is prime, where $\sigma(k^2)$ is the sum of all positive divisors of $k^2$,
and $\phi$ is Euler's totient function.
-/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ (Finset.Icc 1 n).filter (fun k => 2 * k ^ 2 ≤ n),
    let m := n - k ^ 2
    if Nat.Prime (sigma 1 (k ^ 2) + m.totient) then 1 else 0

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by
  unfold a; simp only [sigma_apply, pow_one]; decide

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  unfold a; simp only [sigma_apply, pow_one]; decide

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by
  unfold a; simp only [sigma_apply, pow_one]; decide

@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by
  unfold a; simp only [sigma_apply, pow_one]; decide

@[category test, AMS 11]
theorem a_9 : a 9 = 2 := by
  unfold a; simp only [sigma_apply, pow_one]; decide

/--
Conjecture (i): $a(n) > 0$ for all $n > 1$.
- _Zhi-Wei Sun_
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : 1 < n) : 0 < a n := by
  sorry

/--
Conjecture (ii): Any integer $n > 1$ can be written as $k + m$ with $k > 0$ and $m > 0$
such that $\sigma(k)^2 + \phi(m)$ is prime.
- _Zhi-Wei Sun_
-/
@[category research open, AMS 11]
theorem conjecture2 (n : ℕ) (hn : 1 < n) :
    ∃ k m : ℕ, 0 < k ∧ 0 < m ∧ n = k + m ∧ Nat.Prime (sigma 1 k ^ 2 + m.totient) := by
  sorry

/--
Conjecture (ii): Any integer $n > 1$ can be written as $k + m$ with $k > 0$ and $m > 0$
such that $\sigma(k) + \phi(m)^2$ is prime.
- _Zhi-Wei Sun_
-/
@[category research open, AMS 11]
theorem conjecture3 (n : ℕ) (hn : 1 < n) :
    ∃ k m : ℕ, 0 < k ∧ 0 < m ∧ n = k + m ∧ Nat.Prime (sigma 1 k + m.totient ^ 2) := by
  sorry

end OeisA233544
