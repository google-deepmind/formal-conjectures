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
# Expansion of the e.g.f. $\sin x / \cos 2x$

The sequence lists the odd-index coefficients of $\sin x / \cos 2x$:
$$\frac{\sin x}{\cos 2x} = \sum_{n \ge 0} a(n) \frac{x^{2n+1}}{(2n+1)!},$$
so $a = 1, 11, 361, 24611, \dots$ [Gl14].

*References:*
- [A000464](https://oeis.org/A000464)
- [Gl14] J. W. L. Glaisher, "On the coefficients in the expansions of cos x/ cos 2x and
  sin x/ cos 2x", *Quart. J. Pure Appl. Math.* **45** (1914), 187–222.
- [BG26a] Roberto Blanco Gómez, [Kummer congruences for the values b^r E_r(a/b) of the Euler polynomials at rational points, and the towers a(np^k) ≡ ±a(np^(k-1)) (mod p^k) for the tangent, Euler, zigzag and Springer numbers](https://zenodo.org/records/23407292),
  Zenodo, 2026.
- [BG26b] Roberto Blanco Gómez, [Open statements in core entries of the OEIS, II: further proofs and three refutations](https://zenodo.org/records/23150466),
  Zenodo, 2026.
- [Ka26] Ahaan Kallat, [A Proof of Bala's Congruence Conjectures for A158690](https://arxiv.org/abs/2609.07238),
  arXiv:2609.07238, 2026.
- [Ni26] Yuta Nishibuchi, [A Unified Framework for $p$-adic Congruences and $p$-adic Interpolations of Sequences](https://arxiv.org/abs/2610.11648),
  arXiv:2610.11648, 2026.
- [Do83] A. Dold, [Fixed point indices of iterated maps](https://doi.org/10.1007/BF01394243),
  *Invent. Math.* **74** (1983), 419–435.
-/

@[expose] public section

namespace OeisA464

open PowerSeries

/-- $a(n) = (2n+1)!\,[x^{2n+1}]\, \sin x / \cos 2x$, where $\cos 2x$ is `rescale 2 (cos ℚ)`.
The congruence theorems below state that $a$ is integral by giving an integer sequence `b`
with `(b n : ℚ) = a n` for all `n`. -/
noncomputable def a (n : ℕ) : ℚ :=
  (2 * n + 1).factorial * coeff (2 * n + 1) (sin ℚ * (rescale (2 : ℚ) (cos ℚ))⁻¹)

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by
  sorry

@[category test, AMS 11]
theorem a_1 : a 1 = 11 := by
  sorry

@[category test, AMS 11]
theorem a_2 : a 2 = 361 := by
  sorry

@[category test, AMS 11]
theorem a_3 : a 3 = 24611 := by
  sorry

@[category test, AMS 11]
theorem a_4 : a 4 = 2873041 := by
  sorry

/--
"1) Taking the sequence (a(n))n>=1 modulo an integer k gives a purely periodic sequence with
period dividing phi(k)."
- Peter Bala, Dec 22 2021.

This theorem states that conjecture 1) is false.

Proved by Wentao Li, with AI assistance. Blanco Gómez [BG26b, Theorem 2.2] refuted the same
wording for the Euler numbers A000364.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000020"]
theorem not_conjecture_1 :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ¬ ∀ k : ℕ, 1 ≤ k → ∃ T : ℕ, 0 < T ∧ T ∣ k.totient ∧
        ∀ n : ℕ, 1 ≤ n → b (n + T) ≡ b n [ZMOD k] := by
  sorry

/-- For every multiple $k$ of $81$, the sequence $(a(n))_{n \ge 1}$ modulo $k$ is not purely
periodic with any period $T \ge 1$.

Proved by Wentao Li, with AI assistance. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000020"]
theorem not_periodic_of_eighty_one_dvd :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ k T : ℕ, 81 ∣ k → 0 < T → ¬ ∀ n : ℕ, 1 ≤ n → b (n + T) ≡ b n [ZMOD k] := by
  sorry

/-- The counterexample to conjecture 1): $a(1) = 11$ and $a(55) \equiv 65 \pmod{81}$.

Proved by Wentao Li, with AI assistance. -/
@[category test, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000020"]
theorem a_fifty_five :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧ b 1 = 11 ∧ b 55 ≡ 65 [ZMOD 81] := by
  sorry

/-- The prime $2$: $a(n + 2^{e-1}) \equiv a(n) \pmod{2^e}$ for every $e \ge 1$ and every
$n \ge 0$.

Proved by Wentao Li, with AI assistance. It also follows quickly from Nishibuchi's criterion
[Ni26, Prop. 3.4(1)]. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000020"]
theorem period_two_pow :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ e n : ℕ, 1 ≤ e → b (n + 2 ^ (e - 1)) ≡ b n [ZMOD 2 ^ e] := by
  sorry

/-- The prime $2$, sharper: $a(n + 2^{e-2}) \equiv a(n) \pmod{2^e}$ for every $e \ge 3$ and
every $n \ge 0$.

Proved by Wentao Li, with AI assistance. The proof uses the sufficient direction of
Nishibuchi's criterion [Ni26, Prop. 3.4(1)]. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000020"]
theorem period_two_pow_of_three_le :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ e n : ℕ, 3 ≤ e → b (n + 2 ^ (e - 2)) ≡ b n [ZMOD 2 ^ e] := by
  sorry

/-- Odd primes: $a(n + \frac{p-1}{2} p^{e-1}) \equiv (-1)^{(p-1)/2} a(n) \pmod{p^e}$ for every
odd prime $p$, every $e \ge 1$ and every $n$ with $2n + 1 \ge e$.

Proved by Wentao Li, with AI assistance. The proof uses the $p$-local form of Kallat's method
[Ka26]. The congruence is known: it is the Kummer-type congruence [BG26a, Theorem 1] for the
Euler polynomial values $4^r E_r(1/4)$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000020"]
theorem antiperiod_odd_prime_pow :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ p e n : ℕ, p.Prime → p ≠ 2 → 1 ≤ e → e ≤ 2 * n + 1 →
        b (n + (p - 1) / 2 * p ^ (e - 1)) ≡ (-1) ^ ((p - 1) / 2) * b n [ZMOD p ^ e] := by
  sorry

/-- Odd primes: $a(n + \varphi(p^e)) \equiv a(n) \pmod{p^e}$ for every odd prime $p$, every
$e \ge 1$ and every $n$ with $2n + 1 \ge e$.

Proved by Wentao Li, with AI assistance. It also follows from [BG26a, Theorem 1]. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000020"]
theorem period_odd_prime_pow :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ p e n : ℕ, p.Prime → p ≠ 2 → 1 ≤ e → e ≤ 2 * n + 1 →
        b (n + (p ^ e).totient) ≡ b n [ZMOD p ^ e] := by
  sorry

/--
"1) Taking the sequence (a(n))n>=1 modulo an integer k gives a purely periodic sequence with
period dividing phi(k)."
- Peter Bala, Dec 22 2021.

This theorem states the corrected form: $a(n + \varphi(k)) \equiv a(n) \pmod k$ for every
$k \ge 1$ and every $n$ such that $2n + 1$ is at least the exponent of each odd prime in $k$.

Proved by Wentao Li, with AI assistance. The odd-prime part also follows from
[BG26a, Theorem 1].
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000020"]
theorem period_totient :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ k n : ℕ, 1 ≤ k →
        (∀ p : ℕ, p.Prime → p ≠ 2 → k.factorization p ≤ 2 * n + 1) →
        b (n + k.totient) ≡ b n [ZMOD k] := by
  sorry

/--
"1) Taking the sequence (a(n))n>=1 modulo an integer k gives a purely periodic sequence with
period dividing phi(k)."
- Peter Bala, Dec 22 2021.

This theorem states the eventual form: for every $k \ge 1$, $a(n + \varphi(k)) \equiv a(n)
\pmod k$ for all large $n$.

Proved by Wentao Li, with AI assistance. The odd-prime part also follows from
[BG26a, Theorem 1].
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000020"]
theorem conjecture_1_eventual :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n ≥ N, b (n + k.totient) ≡ b n [ZMOD k] := by
  sorry

/--
"1) Taking the sequence (a(n))n>=1 modulo an integer k gives a purely periodic sequence with
period dividing phi(k)."
- Peter Bala, Dec 22 2021.

This theorem states that the conjecture holds, with period $\varphi(k)$, for every $k \ge 1$
whose odd prime exponents are at most $3$.

Proved by Wentao Li, with AI assistance.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000020"]
theorem conjecture_1_of_exponent_le_three :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ k : ℕ, 1 ≤ k → (∀ p : ℕ, p.Prime → p ≠ 2 → k.factorization p ≤ 3) →
        ∀ n : ℕ, 1 ≤ n → b (n + k.totient) ≡ b n [ZMOD k] := by
  sorry

/--
"1) Taking the sequence (a(n))n>=1 modulo an integer k gives a purely periodic sequence with
period dividing phi(k)."
- Peter Bala, Dec 22 2021.

This theorem states the corrected form with the Carmichael function $\lambda(k)$, a divisor of
$\varphi(k)$: $a(n + \lambda(k)) \equiv a(n) \pmod k$ for every $k \ge 1$ and every $n$ such
that $2n + 1$ is at least the exponent of each odd prime in $k$.

Proved by Wentao Li, with AI assistance.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000020"]
theorem period_carmichael :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ k n : ℕ, 1 ≤ k →
        (∀ p : ℕ, p.Prime → p ≠ 2 → k.factorization p ≤ 2 * n + 1) →
        b (n + ArithmeticFunction.carmichael k) ≡ b n [ZMOD k] := by
  sorry

/--
"1) Taking the sequence (a(n))n>=1 modulo an integer k gives a purely periodic sequence with
period dividing phi(k)."
- Peter Bala, Dec 22 2021.

This theorem states the eventual form with the Carmichael function: for every $k \ge 1$,
$a(n + \lambda(k)) \equiv a(n) \pmod k$ for all large $n$.

Proved by Wentao Li, with AI assistance.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000020"]
theorem conjecture_1_carmichael_eventual :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n ≥ N,
        b (n + ArithmeticFunction.carmichael k) ≡ b n [ZMOD k] := by
  sorry

/-- The period $\lambda(8) = 2$ modulo $8$ cannot be replaced by $1$: $a(1) \not\equiv a(0)
\pmod 8$.

Proved by Wentao Li, with AI assistance. -/
@[category test, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000020"]
theorem carmichael_eight_sharp :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ArithmeticFunction.carmichael 8 = 2 ∧ ¬ b 1 ≡ b 0 [ZMOD 8] := by
  sorry

/--
"2) For i >= 0, define a_i(n) = a(n+i). Then for each i the Gauss congruences
a_i(n*p^k) == a_i(n*p^(k-1)) ( mod p^k ) hold for all prime p and positive integers n and k."
- Peter Bala, Dec 22 2021.

Proved by Wentao Li, with AI assistance. The case of odd $p$ also follows from
[BG26a, Theorem 1].
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000020"]
theorem conjecture_2 :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ i p n k : ℕ, p.Prime → 1 ≤ n → 1 ≤ k →
        b (n * p ^ k + i) ≡ b (n * p ^ (k - 1) + i) [ZMOD p ^ k] := by
  sorry

/--
"2) For i >= 0, define a_i(n) = a(n+i). ... If true, then for each i the expansion of
exp(Sum_{n >= 1} a_i(n)*x^n/n) has integer coefficients."
- Peter Bala, Dec 22 2021.

Here `subst L (exp ℚ)` is $\exp \circ L$.

Proved by Wentao Li, with AI assistance, from `conjecture_2` and Dold's integrality criterion
[Do83].
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000020"]
theorem conjecture_2_exp_integral (i N : ℕ) :
    ∃ z : ℤ, coeff N (subst (mk fun n : ℕ => if n = 0 then (0 : ℚ) else a (n + i) / n)
      (exp ℚ)) = z := by
  sorry

/--
"3) a(m*n) == a(m)^n (mod 2^k) for k = 2*v_2(m) + 4, where v_p(i) denotes the p-adic valuation
of i."
- Peter Bala, Dec 22 2021.

The theorem takes $m, n \ge 1$ and writes $v_2(m)$ as `m.factorization 2`.

Proved by Wentao Li, with AI assistance.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000020"]
theorem conjecture_3 :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
        b (m * n) ≡ b m ^ n [ZMOD 2 ^ (2 * m.factorization 2 + 4)] := by
  sorry

/--
"4)(i) a(2*m*n) == a(n)^(2*m) (mod 2^k) for k = v_2(m) + 4
(ii) a((2*m+1)*n) == a(n)^(2*m+1) (mod 2^k) for k = v_2(m) + 4."
- Peter Bala, Dec 22 2021.

The theorem takes $m, n \ge 1$ and writes $v_2(m)$ as `m.factorization 2`.

Proved by Wentao Li, with AI assistance.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000020"]
theorem conjecture_4 :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
        b (2 * m * n) ≡ b n ^ (2 * m) [ZMOD 2 ^ (m.factorization 2 + 4)] ∧
          b ((2 * m + 1) * n) ≡ b n ^ (2 * m + 1) [ZMOD 2 ^ (m.factorization 2 + 4)] := by
  sorry

end OeisA464

end
