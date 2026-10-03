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
# Scaled binomial sum $\frac{1}{n} \sum_{k=0}^n (n+2k) \binom{n+k-1}{k}^3$

The sequence is defined for $n \ge 1$ by
$$a(n) = \frac{1}{n} \sum_{k=0}^n (n+2k) \binom{n+k-1}{k}^3$$

*References:*
- [A361883](https://oeis.org/A361883)
-/
open Nat Finset

namespace OeisA361883

/--
The sequence $a(n) = \frac{1}{n} \sum_{k=0}^n (n+2k) \binom{n+k-1}{k}^3$.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    -- Calculate the numerator sum S in ℕ
    -- We use binomial(n+k-1, n-1) which is equal to binomial(n+k-1, k)
    -- This makes the dependency on 'n - 1' explicit for the lower index.
    let S : ℕ := ∑ k ∈ range (n + 1),
      (n + 2 * k) * (Nat.choose (n + k - 1) (n - 1)) ^ 3

    -- Division is exact since each term is divisible by n:
    -- (n + 2*k) * choose(n+k-1, k) = n * (choose(n+k, k) + choose(n+k-1, k-1))
    S / n

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 4 := by
  rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 98 := by
  rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 3550 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 150722 := by rfl

/--
The central binomial coefficients $u(n) := \binom{2n}{n}$ satisfy the supercongruences
$u(n \cdot p^r) \equiv u(n \cdot p^{r-1}) \pmod{p^{3r}}$ for positive integers $n$ and $r$
and all primes $p \ge 5$. We conjecture that the present sequence $a(n)$ satisfies the same
congruences.
-/
@[category research open, AMS 11]
theorem supercongruence {p n r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) (hr : 0 < r) :
    a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  sorry

end OeisA361883
