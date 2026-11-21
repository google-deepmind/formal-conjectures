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
# OEIS A339946, Bala's prime-level supercongruence

Peter Bala defines $a(n) = [x^n]\, 1/P_n\bigl(\frac{1-x}{1+x}\bigr)$, where $P_n$ is
the Legendre polynomial. He conjectures $a(p) \equiv a(1) \pmod{p^5}$ for every prime $p \ge 7$
(Dec 2020). In Mar 2022 he extends this: for every positive integer $m$, put
$a_m(n) = [x^{mn}]\, 1/P_n\bigl(\frac{1-x}{1+x}\bigr)$; then $a_m(p) \equiv a_m(1) \pmod{p^5}$ for
all primes $p \ge 7$.

The Legendre polynomial is $P_n(t) = \tilde P_n\bigl(\frac{1-t}{2}\bigr)$, where
$\tilde P_n(x) = \sum_k (-1)^k \binom{n}{k} \binom{n+k}{n} x^k$ is Mathlib's
`Polynomial.shiftedLegendre n` (its Rodrigues formula is
$n!\,\tilde P_n = \frac{d^n}{dx^n}\bigl(x^n (1-x)^n\bigr)$). We evaluate $P_n$ at the power series
$\frac{1-x}{1+x} \in \mathbb{Q}[[x]]$ and invert in $\mathbb{Q}[[x]]$; the constant term is
$P_n(1) = 1$. The values are rational by definition. A congruence $u \equiv v \pmod{p^5}$ is
stated as $u - v = p^5 z$ for an integer $z$.

We also state that the range $p \ge 7$ is optimal: $a_m(5) \equiv 2 + 625 m^2 \pmod{5^5}$, so the
congruence at $p = 5$ holds exactly when $5 \mid m$. This is not a claim of Bala; it records the
sharpness noted with the proof.

*References:*
- Peter Bala, [A339946](https://oeis.org/A339946), Dec 23, 2020, and comment of Mar 10, 2022.
-/

@[expose] public section

namespace OeisA339946

open PowerSeries

/-- The Legendre polynomial $P_n(t) = \tilde P_n\bigl(\frac{1-t}{2}\bigr)$ over $\mathbb{Q}$, with
$\tilde P_n$ = `Polynomial.shiftedLegendre n`. -/
noncomputable def legendreP (n : ℕ) : Polynomial ℚ :=
  (Polynomial.map (Int.castRingHom ℚ) (Polynomial.shiftedLegendre n)).comp
    (Polynomial.C (1 / 2) * (1 - Polynomial.X))

/-- The power series $\frac{1-x}{1+x}$. -/
noncomputable def mobius : ℚ⟦X⟧ := (1 - X) * (1 + X)⁻¹

/-- Bala's $a_m(n) = [x^{mn}]\, 1/P_n\bigl(\frac{1-x}{1+x}\bigr)$. -/
noncomputable def am (m n : ℕ) : ℚ := coeff (m * n) (Polynomial.aeval mobius (legendreP n))⁻¹

/-- OEIS A339946: $a(n) = [x^n]\, 1/P_n\bigl(\frac{1-x}{1+x}\bigr)$. -/
noncomputable def a339946 (n : ℕ) : ℚ := coeff n (Polynomial.aeval mobius (legendreP n))⁻¹

/-- Bala (A339946, Mar 2022): for every $m \ge 1$ and every prime $p \ge 7$,
$a_m(p) \equiv a_m(1) \pmod{p^5}$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000022"]
theorem am_congr (m : ℕ) (hm : 1 ≤ m) (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) :
    ∃ z : ℤ, am m p - am m 1 = (p : ℚ) ^ 5 * z := by
  sorry

/-- Bala (A339946, Dec 2020): for every prime $p \ge 7$, $a(p) \equiv a(1) \pmod{p^5}$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000022"]
theorem a339946_congr (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) :
    ∃ z : ℤ, a339946 p - a339946 1 = (p : ℚ) ^ 5 * z := by
  sorry

/-- Sharpness at $p = 5$: $a_m(5) \equiv 2 + 625 m^2 \pmod{5^5}$ for every $m \ge 1$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000022"]
theorem am_five (m : ℕ) (hm : 1 ≤ m) : ∃ z : ℤ, am m 5 = 2 + 625 * (m : ℚ) ^ 2 + 5 ^ 5 * z := by
  sorry

/-- At $p = 5$, $a_m(5) \equiv a_m(1) \pmod{5^5}$ holds exactly when $5 \mid m$. So $p \ge 7$ is
the optimal uniform range. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000022"]
theorem am_five_congr_iff (m : ℕ) (hm : 1 ≤ m) :
    (∃ z : ℤ, am m 5 - am m 1 = (5 : ℚ) ^ 5 * z) ↔ 5 ∣ m := by
  sorry

end OeisA339946

end
