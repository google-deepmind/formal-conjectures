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
# Number of ways to write $n = p + q$ ($q > 0$) with $p$ and $(\phi(p)\phi(q))^4 + 1$ prime

*References:*
- [A233549](https://oeis.org/A233549)
-/

namespace OeisA233549

/--
The primary defining sequence `a`.
$a(n)$ is the number of ways to write $n = p + q$ ($q > 0$) with $p$ prime and
$(\phi(p)\phi(q))^4 + 1$ prime, where $\phi$ is Euler's totient function.
-/
def a (n : ℕ) : ℕ :=
  Finset.card <| Finset.filter (fun p : ℕ =>
    p.Prime ∧
    let q := n - p
    Nat.Prime ((p.totient * q.totient) ^ 4 + 1)
  ) (Finset.range n)

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 2 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 2 := by decide

/--
Conjecture (i): $a(n) > 0$ for all $n > 2$.
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : 2 < n) : 0 < a n := by
  sorry

/--
Conjecture (ii): If $n > 2$ is not equal to $26$, then there is a prime $p < n$
with $(\phi(p)\phi(n-p))^2 + 1$ prime.
-/
@[category research open, AMS 11]
theorem conjecture2 (n : ℕ) (hn : 2 < n) (hne : n ≠ 26) :
    ∃ p < n, p.Prime ∧ Nat.Prime ((p.totient * (n - p).totient) ^ 2 + 1) := by
  sorry

/--
Conjecture (iii): If $n > 3$ is different from $9$ and $16$, then there is a prime $p < n$
with $((p+1)\phi(n-p))^2 + 1$ prime.
-/
@[category research open, AMS 11]
theorem conjecture3 (n : ℕ) (hn : 3 < n) (hne9 : n ≠ 9) (hne16 : n ≠ 16) :
    ∃ p < n, p.Prime ∧ Nat.Prime (((p + 1) * (n - p).totient) ^ 2 + 1) := by
  sorry

end OeisA233549
