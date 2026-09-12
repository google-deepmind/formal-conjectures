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
# Sum of squared and cubed binomial coefficients

The sequence is defined by
$$a(n) = 3 \sum_{k=0}^n \binom{n+k-1}{k}^2 + 2 \sum_{k=0}^n \binom{n+k-1}{k}^3$$

*References:*
- [A357565](https://oeis.org/A357565)
-/
open Finset Nat

namespace OeisA357565

/--
The sequence $a(n) = 3 \sum_{k=0}^n \binom{n+k-1}{k}^2 + 2 \sum_{k=0}^n \binom{n+k-1}{k}^3$.
-/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1),
    (3 * (choose (n + k - 1) k) ^ 2 + 2 * (choose (n + k - 1) k) ^ 3)

/--
The generalized sequence $u(n, m)$ from the conjecture section:
$u(n, m) = (m + 2) \sum_{k = 0}^{m \cdot n} \binom{n+k-1}{k}^2 + 2m \sum_{k = 0}^{m \cdot n}
\binom{n+k-1}{k}^3$.
Note that $a(n) = u(n, 1)$.
-/
def u (n m : ℕ) : ℕ :=
  ∑ k ∈ range (m * n + 1),
    ((m + 2) * (choose (n + k - 1) k) ^ 2 + (2 * m) * (choose (n + k - 1) k) ^ 3)

@[category test, AMS 11]
theorem a_0 : a 0 = 5 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 10 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 114 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 2926 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 109106 := by rfl

/--
$a(p) \equiv a(1) \pmod{p^5}$ for all odd primes $p$ except $p = 5$.
-/
@[category research open, AMS 11]
theorem conjecture_1 (p : ℕ) (hp : p.Prime) (h_ne2 : p ≠ 2) (h_ne5 : p ≠ 5) :
    (a p) ≡ (a 1) [MOD (p ^ 5)] := by
  sorry
/--
$a(p^r) \equiv a(p^{r-1}) \pmod{p^{3r+3}}$ for $r \ge 2$ and all primes $p \ge 3$.
-/
@[category research open, AMS 11]
theorem conjecture_2 (p r : ℕ) (hp : p.Prime) (h_pge3 : p ≥ 3) (hr : r ≥ 2) :
    (a (p ^ r)) ≡ (a (p ^ (r - 1))) [MOD (p ^ (3 * r + 3))] := by
  sorry
/--
$u(p) \equiv u(1) \pmod{p^5}$ holds for all primes $p \ge 7$ and positive integer $m$.
-/
@[category research open, AMS 11]
theorem conjecture_3 (m p : ℕ) (hm : m > 0) (hp : p.Prime) (h_pge7 : p ≥ 7) :
    (u p m) ≡ (u 1 m) [MOD (p ^ 5)] := by
  sorry
/--
$u(p^r, m) \equiv u(p^{r-1}, m) \pmod{p^{3r+3}}$ for $r \ge 2$, all primes $p \ge 5$, and all
positive integers $m$.

Note: The OEIS entry states this conjecture for $p \ge 3$, but for $(m, p, r) = (2, 3, 2)$
we have $u(9, 2) - u(3, 2) \equiv 2 \cdot 3^8 \not\equiv 0 \pmod{3^9}$, so $p = 3$ fails for $m \ge 2$.
The condition $p \ge 5$ is required for the generalization to hold.
-/
@[category research open, AMS 11]
theorem conjecture_4 (m p r : ℕ) (hm : m > 0) (hp : p.Prime) (h_pge5 : p ≥ 5) (hr : r ≥ 2) :
    (u (p ^ r) m) ≡ (u (p ^ (r - 1)) m) [MOD (p ^ (3 * r + 3))] := by
  sorry

end OeisA357565
