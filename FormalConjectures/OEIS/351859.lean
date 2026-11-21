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
# $[x^n]\, (1 + x + x^2 + x^3)^{4n}/(1 + x + x^2)^{3n}$

The sequence is $a(n) = [x^n]\, G_3(x)^n$, where
$$G_3(x) = \frac{(1 + x + x^2 + x^3)^4}{(1 + x + x^2)^3} \in \mathbb{Z}[[x]].$$
It is the case $k = 3$ of $[x^n]\, G_k(x)^n$ with
$G_k(x) = (1 + x + \dots + x^k)^{k+1}/(1 + x + \dots + x^{k-1})^k$.

*References:*
- [A351859](https://oeis.org/A351859), Peter Bala, 2022.
-/

@[expose] public section

namespace OeisA351859

open PowerSeries

/-- The integer power $F^k$ of a power series $F$ with constant term $1$, for $k \in \mathbb{Z}$.
For $k < 0$ it is $(F^{-1})^{-k}$, where $F^{-1}$ = `invOfUnit F 1`. -/
noncomputable def zpowSeries (F : PowerSeries ℤ) (k : ℤ) : PowerSeries ℤ :=
  if 0 ≤ k then F ^ k.toNat else invOfUnit F 1 ^ k.natAbs

/-- $G_3(x) = (1 + x + x^2 + x^3)^4 / (1 + x + x^2)^3$.
`invOfUnit (1 + X + X ^ 2) 1` is the inverse of $1 + x + x^2$. -/
noncomputable def g : PowerSeries ℤ :=
  (1 + X + X ^ 2 + X ^ 3) ^ 4 * invOfUnit (1 + X + X ^ 2) 1 ^ 3

/-- $a(n) = [x^n]\, (1 + x + x^2 + x^3)^{4n} / (1 + x + x^2)^{3n}$. -/
noncomputable def a (n : ℕ) : ℤ :=
  coeff n ((1 + X + X ^ 2 + X ^ 3) ^ (4 * n) * invOfUnit (1 + X + X ^ 2) 1 ^ (3 * n))

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by
  sorry

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  sorry

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by
  sorry

@[category test, AMS 11]
theorem a_3 : a 3 = 19 := by
  sorry

@[category test, AMS 11]
theorem a_4 : a 4 = 67 := by
  sorry

/-- Bala's $a(r,s;n) = [x^{rn}]\, G_3(x)^{sn}$. -/
noncomputable def b (r : ℕ) (s : ℤ) (n : ℕ) : ℤ := coeff (r * n) (zpowSeries g (s * n))

/--
"Calculation suggests that, in fact, the stronger supercongruences a(n*p^r) == a(n*p^(r-1))
(mod p^(3*r)) hold for primes p >= 5 and positive integers n and r."
- Peter Bala, Mar 01 2022.

Proved by Wentao Li, with AI assistance. The proof builds on the $p^{2k}$ towers of rbajaj5 and
R. Blanco Gómez and follows rbajaj5's proof for A351858 (October 2026).
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000017"]
theorem conjecture (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ a (n * p ^ k) - a (n * p ^ (k - 1)) := by
  sorry

/--
"More generally, if r is a positive integer and s an integer then the sequence defined by
a(r,s;n) = [x^(r*n)] G_3(x)^(s*n) may satisfy the same supercongruences."
- Peter Bala, Mar 01 2022.

This theorem states them for primes $p \ge 5$, the range of `conjecture`.

Proved by Wentao Li, with AI assistance. The proof builds on the $p^{2k}$ towers of rbajaj5 and
R. Blanco Gómez and follows rbajaj5's proof for A351858 (October 2026).
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000017"]
theorem conjecture_rs (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (r : ℕ) (hr : 0 < r) (s : ℤ)
    (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ b r s (n * p ^ k) - b r s (n * p ^ (k - 1)) := by
  sorry

end OeisA351859

end
