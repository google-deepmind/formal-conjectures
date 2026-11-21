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
# Coefficients of $1/P_n\bigl(\frac{1-x}{1+x}\bigr)$

Let $P_n$ be the Legendre polynomial. The sequence is
$a(n) = [x^n]\, 1/P_n\bigl(\frac{1-x}{1+x}\bigr)$ for $n \ge 1$.

*References:*
- [A339946](https://oeis.org/A339946), Peter Bala, 2020.
-/

@[expose] public section

namespace OeisA339946

open PowerSeries

/-- The Legendre polynomial $P_n(t) = \tilde P_n\bigl(\frac{1-t}{2}\bigr)$ over $\mathbb{Q}$, where
$\tilde P_n(x) = \sum_k (-1)^k \binom{n}{k} \binom{n+k}{n} x^k$ is the shifted Legendre polynomial
`Polynomial.shiftedLegendre n`. -/
noncomputable def legendreP (n : ℕ) : Polynomial ℚ :=
  (Polynomial.map (Int.castRingHom ℚ) (Polynomial.shiftedLegendre n)).comp
    (Polynomial.C (1 / 2) * (1 - Polynomial.X))

/-- The power series $\frac{1-x}{1+x}$. -/
noncomputable def mobius : ℚ⟦X⟧ := (1 - X) * (1 + X)⁻¹

/-- $a(n) = [x^n]\, 1/P_n\bigl(\frac{1-x}{1+x}\bigr)$. The inverse is taken in $\mathbb{Q}[[x]]$,
where $P_n\bigl(\frac{1-x}{1+x}\bigr)$ has constant term $P_n(1) = 1$. -/
noncomputable def a (n : ℕ) : ℚ := coeff n (Polynomial.aeval mobius (legendreP n))⁻¹

@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by
  sorry

@[category test, AMS 11]
theorem a_2 : a 2 = 24 := by
  sorry

@[category test, AMS 11]
theorem a_3 : a 3 = 812 := by
  sorry

@[category test, AMS 11]
theorem a_4 : a 4 = 52920 := by
  sorry

@[category test, AMS 11]
theorem a_5 : a 5 = 5635002 := by
  sorry

/--
"Calculation suggests that, for the present sequence, we have stronger congruences for prime
p >= 7, namely a(p) == a(1) ( mod p^5 ) (checked up to p = 61)."
- Peter Bala, Dec 23 2020.

The values of `a` lie in $\mathbb{Q}$, so the congruence is stated as $a(p) - a(1) = p^5 z$ for
an integer $z$.

Proved by Wentao Li, with AI assistance.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000022"]
theorem conjecture (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) :
    ∃ z : ℤ, a p - a 1 = (p : ℚ) ^ 5 * z := by
  sorry

/-- Bala's $a_m(n) = [x^{mn}]\, 1/P_n\bigl(\frac{1-x}{1+x}\bigr)$. The case $m = 1$ is `a`. -/
noncomputable def am (m n : ℕ) : ℚ := coeff (m * n) (Polynomial.aeval mobius (legendreP n))⁻¹

/--
"For m a positive integer, define a_m(n) = [x^(m*n)] 1/Legendre_P(n,(1 - x)/(1 + x)). We
conjecture that the supercongruence a_m(p) == a_m(1) ( mod p^5 ) holds for all primes p >= 7."
- Peter Bala, Mar 10 2022.

As in `conjecture`, the congruence is stated as $a_m(p) - a_m(1) = p^5 z$ for an integer $z$.

Proved by Wentao Li, with AI assistance.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000022"]
theorem conjecture_am (m : ℕ) (hm : 1 ≤ m) (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) :
    ∃ z : ℤ, am m p - am m 1 = (p : ℚ) ^ 5 * z := by
  sorry

/-- For every $m \ge 1$, $a_m(5) \equiv 2 + 625 m^2 \pmod{5^5}$.

Proved by Wentao Li, with AI assistance. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000022"]
theorem am_five (m : ℕ) (hm : 1 ≤ m) : ∃ z : ℤ, am m 5 = 2 + 625 * (m : ℚ) ^ 2 + 5 ^ 5 * z := by
  sorry

/-- For every $m \ge 1$, $a_m(5) \equiv a_m(1) \pmod{5^5}$ holds exactly when $5 \mid m$. So the
bound $p \ge 7$ in `conjecture_am` cannot be lowered.

Proved by Wentao Li, with AI assistance. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000022"]
theorem am_five_congr_iff (m : ℕ) (hm : 1 ≤ m) :
    (∃ z : ℤ, am m 5 - am m 1 = (5 : ℚ) ^ 5 * z) ↔ 5 ∣ m := by
  sorry

end OeisA339946

end
