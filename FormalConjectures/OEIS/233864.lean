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
# Values $m = \sigma(k)$ ($0 < m < 2n$) with $2n - 1 - m$ and $2n - 1 + m$ prime

*References:*
- [A233864](https://oeis.org/A233864)
-/

namespace OeisA233864

open ArithmeticFunction

/--
The primary defining sequence `a`.
$a(n)$ is the number of integers $m$ with $0 < m < 2n$ such that $m = \sigma(k)$ for some $k > 0$,
and both $2n - 1 - m$ and $2n - 1 + m$ are prime, where $\sigma(k)$ is the sum of the positive
divisors of $k$.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let twiceN : ℕ := 2 * n
    let bigN : ℕ := twiceN - 1
    let kDomain : Finset ℕ := Finset.Ico 1 twiceN
    let sigmaValues : Finset ℕ := kDomain.image (sigma 1)
    (sigmaValues.filter (fun m : ℕ =>
      m < bigN ∧
      (bigN - m).Prime ∧
      (bigN + m).Prime
    )).card

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by rfl

@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by rfl

/--
Conjecture (i): $a(n) > 0$ for all $n > 3$.
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : 3 < n) : 0 < a n := by
  sorry

/--
Conjecture (ii): For any even number $2n > 0$, $2n + \sigma(k)$ is prime for some $0 < k < 2n$.
-/
@[category research open, AMS 11]
theorem conjecture2 (n : ℕ) (hn : 0 < n) :
    ∃ k, 0 < k ∧ k < 2 * n ∧ Nat.Prime (2 * n + sigma 1 k) := by
  sorry

end OeisA233864
