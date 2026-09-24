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
# Linear combination of Apéry numbers $5 A(n) + 14 B(n-1)$

The sequence is defined by $a(n) = 5 A(n) + 14 B(n-1)$, where $A(n)$ are the Apéry numbers for
$\zeta(3)$
(A005259) and $B(n)$ are the Apéry numbers for $\zeta(2)$ (A005258).

*References:*
- [A357958](https://oeis.org/A357958)
-/
open Nat Finset

namespace OeisA357958

/--
The Apéry number sequence $A(n) = \sum_{k = 0}^n \binom{n}{k}^2 \binom{n+k}{k}^2$.
-/
def A005259_seq (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), (n.choose k) ^ 2 * ((n + k).choose k) ^ 2

/--
The related Apéry number sequence $C(n) = \sum_{k = 0}^n \binom{n}{k}^2 \binom{n+k}{k}$.
-/
def A005258_seq (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), (n.choose k) ^ 2 * ((n + k).choose k)

/--
The sequence $a(n) = 5 A(n) + 14 B(n-1)$.
-/
def a (n : ℕ) : ℕ :=
  5 * A005259_seq n + 14 * A005258_seq (n - 1)

/--
The sequence $u(n)$ defined by $u(n) = A(n)^{25} B(n-1)^{14}$.
-/
def u (n : ℕ) : ℕ :=
  (A005259_seq n) ^ 25 * (A005258_seq (n - 1)) ^ 14

@[category test, AMS 11]
theorem a_1 : a 1 = 39 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 407 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 7491 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 167063 := by rfl

@[category test, AMS 11]
theorem a_5 : a 5 = 4112539 := by rfl

/--
$a(p) \equiv a(1) \pmod{p^5}$ for all primes $p \ge 5$.
-/
@[category research open, AMS 11]
theorem conjecture_1 :
  ∀ (p : ℕ), p.Prime → 5 ≤ p → (a p) ≡ (a 1) [MOD p^5] :=
by sorry

/--
$a(p^r) \equiv a(p^{r-1}) \pmod{p^{3r+3}}$ for $r \ge 2$ and for all primes $p \ge 3$.
-/
@[category research open, AMS 11]
theorem conjecture_2 :
  ∀ (p r : ℕ), p.Prime → 3 ≤ p → 2 ≤ r → (a (p^r)) ≡ (a (p^(r-1))) [MOD p^(3*r + 3)] :=
by sorry

/--
$u(p) \equiv u(1) \pmod{p^5}$ for all primes $p \ge 5$.
-/
@[category research open, AMS 11]
theorem conjecture_3a :
  ∀ (p : ℕ), p.Prime → 5 ≤ p → (u p) ≡ (u 1) [MOD p^5] :=
by sorry

/--
$u(p^r) \equiv u(p^{r-1}) \pmod{p^{3r+3}}$ for $r \ge 2$ and for all primes $p \ge 5$
(at $p = 3$, the valuation is $3r + 2$).
-/
@[category research open, AMS 11]
theorem conjecture_3b :
  ∀ (p r : ℕ), p.Prime → 5 ≤ p → 2 ≤ r → (u (p^r)) ≡ (u (p^(r-1))) [MOD p^(3*r + 3)] :=
by sorry

end OeisA357958
