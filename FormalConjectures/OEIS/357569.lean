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
# Binomial difference $\binom{3n}{n}^2 - 27\binom{2n}{n}$

The sequence is defined by
$$a(n) = \binom{3n}{n}^2 - 27 \binom{2n}{n}$$

*References:*
- [A357569](https://oeis.org/A357569)
-/
open Nat

namespace OeisA357569

/--
The sequence $a(n) = \binom{3n}{n}^2 - 27 \binom{2n}{n}$.
-/
def a (n : ℕ) : ℤ :=
  (((3 * n).choose n : ℤ)) ^ 2 - (27 : ℤ) * ((2 * n).choose n : ℤ)

@[category test, AMS 11]
theorem a_0 : a 0 = -26 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = -45 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 63 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 6516 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 243135 := by rfl

/--
The generalized sequence $u(k, n) = 2 \binom{3n}{n}^k - k \cdot 3^{k+1} \binom{2n}{n}$ for $k
\ge 1$.
Note that $u(2, n) = 2 \cdot a(n)$.
-/
def u (k n : ℕ) : ℤ :=
  2 * (((3 * n).choose n : ℤ)) ^ k -
  (k : ℤ) * ((3 : ℤ) ^ (k + 1)) * ((2 * n).choose n : ℤ)

/-- $a(p^r) \equiv a(p^{r-1}) \pmod{p^{3r+3}}$ for $r \ge 2$ and all primes $p \ge 3$. -/
@[category research open, AMS 11]
theorem conjecture_1 (p r : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) (hr : r ≥ 2) :
  a (p ^ r) ≡ a (p ^ (r - 1)) [ZMOD ((p : ℤ) ^ (3 * r + 3))] :=
by sorry

/--
For $k \ge 1$, the sequence $u(k, n)$ satisfies the same supercongruences
$u(k, p^r) \equiv u(k, p^{r-1}) \pmod{p^{3r+3}}$ for $r \ge 2$ and all primes $p \ge 3$.
-/
@[category research open, AMS 11]
theorem conjecture_2 (k p r : ℕ) (hk : k ≥ 1) (hp : p.Prime) (hp3 : p ≥ 3) (hr : r ≥ 2) :
  u k (p ^ r) ≡ u k (p ^ (r - 1)) [ZMOD ((p : ℤ) ^ (3 * r + 3))] :=
by sorry

end OeisA357569
