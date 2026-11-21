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
# Glaisher's $T$ numbers

The sequence lists the odd-index coefficients of $\sin 2x / (2 \cos 3x)$:
$$\frac{\sin 2x}{2 \cos 3x} = \sum_{n \ge 0} a(n) \frac{x^{2n+1}}{(2n+1)!},$$
so $a = 1, 23, 1681, 257543, \dots$ [Gl99]. Equivalently,
$a(n) = \frac{(-1)^{n+1}}{2} L(-2n-1, \chi_{12})$, where $\chi_{12}$ is the real Dirichlet
character modulo $12$ with $\chi_{12}(\pm 1) = 1$ and $\chi_{12}(\pm 5) = -1$.

*References:*
- [A002439](https://oeis.org/A002439)
- [Gl99] J. W. L. Glaisher, [On a set of coefficients analogous to the Eulerian numbers](https://doi.org/10.1112/plms/s1-31.1.216),
  *Proc. London Math. Soc.* **31** (1899), 216–235.
- [BG26] Roberto Blanco Gómez, [Kummer congruences for the values b^r E_r(a/b) of the Euler polynomials at rational points, and the towers a(np^k) ≡ ±a(np^(k-1)) (mod p^k) for the tangent, Euler, zigzag and Springer numbers](https://zenodo.org/records/23407292),
  Zenodo, 2026.
-/

@[expose] public section

namespace OeisA2439

open PowerSeries

/-- $a(n) = (2n+1)!\,[x^{2n+1}]\, \sin 2x / (2 \cos 3x)$, where $\sin 2x$ is
`rescale 2 (sin ℚ)` and $\cos 3x$ is `rescale 3 (cos ℚ)`. The congruence theorems below state
that $a$ is integral by giving an integer sequence `b` with `(b n : ℚ) = a n` for all `n`. -/
noncomputable def a (n : ℕ) : ℚ :=
  (2 * n + 1).factorial *
    coeff (2 * n + 1) (rescale (2 : ℚ) (sin ℚ) * (2 * rescale (3 : ℚ) (cos ℚ))⁻¹)

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by
  sorry

@[category test, AMS 11]
theorem a_1 : a 1 = 23 := by
  sorry

@[category test, AMS 11]
theorem a_2 : a 2 = 1681 := by
  sorry

@[category test, AMS 11]
theorem a_3 : a 3 = 257543 := by
  sorry

@[category test, AMS 11]
theorem a_4 : a 4 = 67637281 := by
  sorry

/-- The Dirichlet character $\chi_{12}$ at an integer $p$ prime to $6$: $\chi_{12}(p) = 1$ if
$p \equiv \pm 1 \pmod{12}$ and $\chi_{12}(p) = -1$ if $p \equiv \pm 5 \pmod{12}$. -/
def chi12 (p : ℕ) : ℤ := if p % 12 = 1 ∨ p % 12 = 11 then 1 else -1

/--
"3)(i) a(m*n) == a(m)^n (mod 2^k) for k = 2*v_2(m) + 7, where v_p(i) denotes the p-adic
valuation of i."
- Peter Bala, Dec 18 2021.

The theorem takes $m, n \ge 1$ and writes $v_2(m)$ as `m.factorization 2`.

Proved by Wentao Li, with AI assistance.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000002"]
theorem conjecture_3_two :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
        b (m * n) ≡ b m ^ n [ZMOD 2 ^ (2 * m.factorization 2 + 7)] := by
  sorry

/--
"3)(i) ... (ii) a(m*n) == a(m)^n (mod 3^k) for k = 2*v_3(m) + 2."
- Peter Bala, Dec 18 2021.

The theorem takes $m, n \ge 1$ and writes $v_3(m)$ as `m.factorization 3`.

Proved by Wentao Li, with AI assistance.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000002"]
theorem conjecture_3_three :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
        b (m * n) ≡ b m ^ n [ZMOD 3 ^ (2 * m.factorization 3 + 2)] := by
  sorry

/--
"4)(i) a(2*m*n) == a(n)^(2*m) (mod 2^k) for k = v_2(m) + 7
(ii) a((2*m+1)*n) == a(n)^(2*m+1) (mod 2^k) for k = v_2(m) + 7."
- Peter Bala, Dec 18 2021.

The theorem takes $m, n \ge 1$ and writes $v_2(m)$ as `m.factorization 2`.

Proved by Wentao Li, with AI assistance.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000002"]
theorem conjecture_4 :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
        b (2 * m * n) ≡ b n ^ (2 * m) [ZMOD 2 ^ (m.factorization 2 + 7)] ∧
          b ((2 * m + 1) * n) ≡ b n ^ (2 * m + 1) [ZMOD 2 ^ (m.factorization 2 + 7)] := by
  sorry

/--
"5)(i) a(3*m*n) == a(n)^(3*m) (mod 3^k) for k = v_3(m) + 2
(ii) a((3*m+1)*n) == a(n)^(3*m+1) (mod 3^k) for k = v_3(m) + 2"
- Peter Bala, Dec 18 2021.

The theorem takes $m, n \ge 1$ and writes $v_3(m)$ as `m.factorization 3`.

Proved by Wentao Li, with AI assistance.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000002"]
theorem conjecture_5 :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
        b (3 * m * n) ≡ b n ^ (3 * m) [ZMOD 3 ^ (m.factorization 3 + 2)] ∧
          b ((3 * m + 1) * n) ≡ b n ^ (3 * m + 1) [ZMOD 3 ^ (m.factorization 3 + 2)] := by
  sorry

/--
"5)(i) ... (iii) a((3*m+2)*n) == a(n)^(3*m+2) (mod 3^2)."
- Peter Bala, Dec 18 2021.

The theorem takes $m \ge 0$ and $n \ge 1$, since the modulus does not depend on $m$; the case
$m = 0$ is $a(2n) \equiv a(n)^2 \pmod 9$.

Proved by Wentao Li, with AI assistance.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000002"]
theorem conjecture_5_iii :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ m n : ℕ, 1 ≤ n → b ((3 * m + 2) * n) ≡ b n ^ (3 * m + 2) [ZMOD 9] := by
  sorry

/--
"a(n) == 23^n ( mod (2^7)*(3^2) )."
- Peter Bala, Dec 25 2021.

Here $2^7 \cdot 3^2 = 1152$.

Proved by Wentao Li, with AI assistance.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000002"]
theorem a_mod_1152 :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧ ∀ n : ℕ, b n ≡ 23 ^ n [ZMOD 1152] := by
  sorry

/--
"6) For prime p >= 5, a((p-1)/2*n*m) == a((p-1)/2*n)^m (mod p^k) for k = v_p(m-1) + 1."
- Peter Bala, Dec 18 2021.

This theorem states that conjecture 6), read for all $m, n \ge 1$, is false. Here $v_p(m-1)$ is
`(m - 1).factorization p`, which is $0$ at $m = 1$.

Proved by Wentao Li, with AI assistance.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000002"]
theorem not_conjecture_6 :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ¬ ∀ p m n : ℕ, p.Prime → 5 ≤ p → 1 ≤ m → 1 ≤ n →
        b ((p - 1) / 2 * n * m) ≡ b ((p - 1) / 2 * n) ^ m
          [ZMOD p ^ ((m - 1).factorization p + 1)] := by
  sorry

/-- The counterexample to conjecture 6) at $p = 5$, $n = 1$, $m = 3126$: $a(2) = 1681$,
$a(6252) \equiv (1 + 5^5)\,a(2) \pmod{5^6}$, and $v_5(a(6252) - a(2)^{3126}) = 5$, while 6)
asks for $v_5 \ge v_5(3125) + 1 = 6$.

Proved by Wentao Li, with AI assistance. -/
@[category test, AMS 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000002"]
theorem conjecture_6_counterexample :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧ b 2 = 1681 ∧
      b 6252 ≡ (1 + 5 ^ 5) * b 2 [ZMOD 5 ^ 6] ∧ padicValInt 5 (b 6252 - b 2 ^ 3126) = 5 := by
  sorry

/-- Odd primes: $a(n + \frac{p-1}{2} p^{e-1}) \equiv (-1)^{(p-1)/2} a(n) \pmod{p^e}$ for every
odd prime $p$, every $e \ge 1$ and every $n$ with $2n + 1 \ge e$.

Proved by Wentao Li, with AI assistance. For $p \ge 5$ the congruence is known: it is the
Kummer-type congruence [BG26, Theorem 1] for the Euler polynomial values $6^r E_r(1/6)$. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000002"]
theorem antiperiod_odd_prime_pow :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ p e n : ℕ, p.Prime → p ≠ 2 → 1 ≤ e → e ≤ 2 * n + 1 →
        b (n + (p - 1) / 2 * p ^ (e - 1)) ≡ (-1) ^ ((p - 1) / 2) * b n [ZMOD p ^ e] := by
  sorry

/--
"6) For prime p >= 5, a((p-1)/2*n*m) == a((p-1)/2*n)^m (mod p^k) for k = v_p(m-1) + 1."
- Peter Bala, Dec 18 2021.

This theorem states the corrected form: the congruence holds for all $m, n \ge 1$ with
$v_p(m-1) \le (p-1) n$.

Proved by Wentao Li, with AI assistance. It is a short corollary of [BG26, Theorem 1].
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000002"]
theorem conjecture_6_of_le :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ p m n : ℕ, p.Prime → 5 ≤ p → 1 ≤ m → 1 ≤ n → (m - 1).factorization p ≤ (p - 1) * n →
        b ((p - 1) / 2 * n * m) ≡ b ((p - 1) / 2 * n) ^ m
          [ZMOD p ^ ((m - 1).factorization p + 1)] := by
  sorry

/-- For every prime $p \ge 5$, with $h = (p-1)/2$, every $e \ge 1$ and every $n \ge 0$,
$a(n + h p^{e-1}) \equiv (-1)^h \big(1 - \chi_{12}(p)\, p^{2n+1}\big)\, a(n) \pmod{p^e}$.

Proved by Wentao Li, with AI assistance, from an elementary alternating-sum formula. This is the
classical Kummer congruence for these $L$-values, with Euler factor $1 - \chi_{12}(p) p^{2n+1}$.
For $2n + 1 \ge e$ it is a case of [BG26, Theorem 1]. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000002"]
theorem antiperiod_euler :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ p e n : ℕ, p.Prime → 5 ≤ p → 1 ≤ e →
        b (n + (p - 1) / 2 * p ^ (e - 1)) ≡
          (-1) ^ ((p - 1) / 2) * (1 - chi12 p * (p : ℤ) ^ (2 * n + 1)) * b n [ZMOD p ^ e] := by
  sorry

/--
"6) For prime p >= 5, a((p-1)/2*n*m) == a((p-1)/2*n)^m (mod p^k) for k = v_p(m-1) + 1."
- Peter Bala, Dec 18 2021.

This theorem states the exact range: for $m, n \ge 1$ the congruence holds if and only if
$v_p(m-1) \le (p-1) n$.

Proved by Wentao Li, with AI assistance. It is a short consequence of the classical Kummer
congruence `antiperiod_euler`.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000002"]
theorem conjecture_6_iff :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ p m n : ℕ, p.Prime → 5 ≤ p → 1 ≤ m → 1 ≤ n →
        (b ((p - 1) / 2 * n * m) ≡ b ((p - 1) / 2 * n) ^ m
          [ZMOD p ^ ((m - 1).factorization p + 1)] ↔ (m - 1).factorization p ≤ (p - 1) * n) := by
  sorry

/-- The prime $3$: $a(n + 3^{e-1}) \equiv -a(n) \pmod{3^e}$ for every $e \ge 1$ and every
$n \ge 0$.

Proved by Wentao Li, with AI assistance. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000002"]
theorem antiperiod_three :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ e n : ℕ, 1 ≤ e → b (n + 3 ^ (e - 1)) ≡ -b n [ZMOD 3 ^ e] := by
  sorry

/--
"5)(i) a(3*m*n) == a(n)^(3*m) (mod 3^k) for k = v_3(m) + 2
(ii) a((3*m+1)*n) == a(n)^(3*m+1) (mod 3^k) for k = v_3(m) + 2"
- Peter Bala, Dec 18 2021.

This theorem states 5)(i) and (ii) with one more power of $3$, modulo $3^{v_3(m) + 3}$, for all
$m, n \ge 1$.

Proved by Wentao Li, with AI assistance.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000002"]
theorem conjecture_5_strong :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
        b (3 * m * n) ≡ b n ^ (3 * m) [ZMOD 3 ^ (m.factorization 3 + 3)] ∧
          b ((3 * m + 1) * n) ≡ b n ^ (3 * m + 1) [ZMOD 3 ^ (m.factorization 3 + 3)] := by
  sorry

end OeisA2439

end
