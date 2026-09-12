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
# Product of powers of binomial sums

The sequence is defined by
$$a(n) = \left( \sum_{k=0}^{2n} \binom{n+k-1}{k} \right)^4
  \left( \sum_{k=0}^{2n} \binom{n+k-1}{k}^2 \right)^3$$

*References:*
- [A357674](https://oeis.org/A357674)
-/
open Nat Finset

namespace OeisA357674

/--
The sequence $a(n) = \left( \sum_{k=0}^{2n} \binom{n+k-1}{k} \right)^4 \left( \sum_{k=0}^{2n}
\binom{n+k-1}{k}^2 \right)^3$.
-/
def a (n : ℕ) : ℕ :=
  let S1 : ℕ := ∑ k ∈ range (2 * n + 1), (n + k - 1).choose k
  let S2 : ℕ := ∑ k ∈ range (2 * n + 1), ((n + k - 1).choose k) ^ 2
  S1 ^ 4 * S2 ^ 3

/--
The general sequence $u(n, m)$ from conjecture 3.
$u(n, m) = \left( \sum_{k = 0}^{m*n} \binom{n+k-1}{k} \right)^{2m} \cdot \left( \sum_{k =
0}^{m*n} \binom{n+k-1}{k}^2 \right)^{m+1}$.
Note that `a n = u n 2`.
-/
def u (n m : ℕ) : ℕ :=
  let S1 : ℕ := ∑ k ∈ range (m * n + 1), (n + k - 1).choose k
  let S2 : ℕ := ∑ k ∈ range (m * n + 1), ((n + k - 1).choose k) ^ 2
  S1 ^ (2 * m) * S2 ^ (m + 1)

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by
  rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 2187 := by
  rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 8422734375 := by
  rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 202402468703748096 := by
  rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 9223976224194016590174375 := by rfl

/--
$a(p) \equiv a(1) \pmod{p^5}$ for all primes $p \ge 3$.
-/
@[category research open, AMS 11]
theorem conjecture_1 (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    a p ≡ a 1 [MOD p ^ 5] := by
  sorry

/--
For $r \ge 2$, and all primes $p \ge 3$, $a(p^r) \equiv a(p^{r-1}) \pmod{p^{3r+3}}$.
We interpret $p^{r-1}$ using `Nat.pow p (r - 1)`.
-/
@[category research open, AMS 11]
theorem conjecture_2 (p r : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) (hr : r ≥ 2) :
    a (p ^ r) ≡ a (p ^ (r - 1)) [MOD p ^ (3 * r + 3)] := by
  sorry

/--
Let $m$ be a positive integer and set $u(n) = \left( \sum_{k = 0}^{m*n} \binom{n+k-1}{k}
\right)^{2m} \cdot \left( \sum_{k = 0}^{m*n} \binom{n+k-1}{k}^2 \right)^{m+1}$.
Then the sequence $\{u(n, m)\}$ satisfies the supercongruence $u(p, m) \equiv u(1, m) \pmod{p^5}$
for all primes $p \ge 7$. This is the case $m = 2$.
-/
@[category research open, AMS 11]
theorem conjecture_3 (p m : ℕ) (hp : p.Prime) (hp7 : p ≥ 7) (hm : m ≥ 1) :
    u p m ≡ u 1 m [MOD p ^ 5] := by
  sorry

end OeisA357674
