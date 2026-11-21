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
module

public import FormalConjecturesUtil

/-!
# $[x^n]\, f(x)^n$ for $f(x) = (1 - x^7)^7/((1 - x^3)^3 (1 - x^4)^4)$

The sequence is $a(n) = [x^n]\, f(x)^n$, where
$$f(x) = \frac{(1 - x^7)^7}{(1 - x^3)^3\,(1 - x^4)^4} \in \mathbb{Z}[[x]].$$

*References:*
- [A372213](https://oeis.org/A372213), Peter Bala, 2024.
-/

@[expose] public section

namespace OeisA372213

open PowerSeries

/-- The integer power $F^k$ of a power series $F$ with constant term $1$, for $k \in \mathbb{Z}$.
For $k < 0$ it is $(F^{-1})^{-k}$, where $F^{-1}$ = `invOfUnit F 1`. -/
noncomputable def zpowSeries (F : PowerSeries ℤ) (k : ℤ) : PowerSeries ℤ :=
  if 0 ≤ k then F ^ k.toNat else invOfUnit F 1 ^ k.natAbs

/-- The series $f(x) = (1 - x^7)^7 / ((1 - x^3)^3\,(1 - x^4)^4)$.
`invOfUnit (1 - X ^ e) 1` is the inverse of $1 - x^e$. -/
noncomputable def f : PowerSeries ℤ :=
  (1 - X ^ 7) ^ 7 * invOfUnit (1 - X ^ 3) 1 ^ 3 * invOfUnit (1 - X ^ 4) 1 ^ 4

/-- $a(n) = [x^n]\, f(x)^n$. -/
noncomputable def a (n : ℕ) : ℤ := coeff n (f ^ n)

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by
  sorry

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by
  sorry

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by
  sorry

@[category test, AMS 11]
theorem a_3 : a 3 = 9 := by
  sorry

@[category test, AMS 11]
theorem a_4 : a 4 = 16 := by
  sorry

/-- Bala's $u(r,s;n) = [x^{rn}]\, f(x)^{sn}$. -/
noncomputable def b (r : ℕ) (s : ℤ) (n : ℕ) : ℤ :=
  coeff (r * n) (zpowSeries f (s * n))

/--
"We conjecture that in this case the stronger supercongruences a(n*p^r) == a(n*p^(r-1))
(mod p^(3*r)) hold for primes p >= 11 and positive integers n and r."
- Peter Bala, Apr 22 2024.

This theorem states the supercongruences for every prime $p \ge 5$ with $p \ne 7$, which
includes Bala's range.

Proved by Wentao Li, with AI assistance. The proof builds on the $p^{2k}$ towers of rbajaj5 and
R. Blanco Gómez and follows rbajaj5's proof for A351858 (October 2026).
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000017"]
theorem conjecture (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (h7 : p ≠ 7) (n k : ℕ) (hn : 0 < n)
    (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ a (n * p ^ k) - a (n * p ^ (k - 1)) := by
  sorry

/--
"More generally, if r is a positive integer and s an integer then the sequence defined
by  u(r,s; n) = [x^(r*n)] f(x)^(s*n) may satisfy the same supercongruences."
- Peter Bala, Apr 22 2024.

This theorem states them for every prime $p \ge 5$ with $p \ne 7$, which includes the range
$p \ge 11$ of `conjecture`.

Proved by Wentao Li, with AI assistance. The proof builds on the $p^{2k}$ towers of rbajaj5 and
R. Blanco Gómez and follows rbajaj5's proof for A351858 (October 2026).
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000017"]
theorem conjecture_rs (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (h7 : p ≠ 7) (r : ℕ) (hr : 0 < r)
    (s : ℤ) (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ b r s (n * p ^ k) - b r s (n * p ^ (k - 1)) := by
  sorry

end OeisA372213

end
