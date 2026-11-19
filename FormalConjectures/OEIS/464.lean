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
# OEIS A000464, Bala's conjectures for $\sin x / \cos 2x$

OEIS A000464 is the expansion of the e.g.f. $\sin x / \cos 2x$. Its terms are the odd-index
coefficients, with offset $0$: $a(n) = (2n+1)!\,[x^{2n+1}]\, \sin x / \cos 2x$, so
$a = 1, 11, 361, 24611, \dots$ (J. W. L. Glaisher, 1914).
Peter Bala (OEIS, December 22, 2021) made these conjectures:
1. $(a(n))_{n \ge 1}$ reduced modulo $k$ is purely periodic with period dividing $\varphi(k)$,
   for every integer $k \ge 1$.
2. For every $i \ge 0$, the shifted sequence $a_i(n) = a(n + i)$ satisfies the Gauss
   congruences $a_i(n p^k) \equiv a_i(n p^{k-1}) \pmod{p^k}$ for all primes $p$ and all
   $n, k \ge 1$. Then $\exp\left(\sum_{n \ge 1} a_i(n) x^n / n\right)$ has integer
   coefficients.
3. $a(mn) \equiv a(m)^n \pmod{2^k}$ for $k = 2 v_2(m) + 4$.
4. $a(2mn) \equiv a(n)^{2m}$ and $a((2m+1)n) \equiv a(n)^{2m+1} \pmod{2^k}$ for
   $k = v_2(m) + 4$.

The file states:
- conjecture 1) is false as stated (`not_conjecture1`). For every multiple $k$ of $81$, the
  sequence $(a(n))_{n \ge 1}$ modulo $k$ is not purely periodic with any period
  (`not_periodic_of_eighty_one_dvd`). The witness is $a(55) \equiv 65 \pmod{81}$ while
  $a(1) = 11$ (`a_fifty_five`);
- the prime-power congruences: $a(n + 2^{e-1}) \equiv a(n) \pmod{2^e}$ for every $n$
  (`period_two_pow`), and $a(n + 2^{e-2}) \equiv a(n) \pmod{2^e}$ when $e \ge 3$
  (`period_two_pow_of_three_le`); $a(n + \frac{p-1}{2} p^{e-1}) \equiv (-1)^{(p-1)/2} a(n)
  \pmod{p^e}$ for odd primes $p$ and $2n + 1 \ge e$ (`antiperiod_odd_prime_pow`), hence
  $a(n + \varphi(p^e)) \equiv a(n) \pmod{p^e}$ (`period_odd_prime_pow`);
- the corrected conjecture 1): $a(n + \varphi(k)) \equiv a(n) \pmod k$ whenever $2n + 1$ is at
  least the exponent of every odd prime in $k$ (`period_totient`). So 1) holds in its eventual
  form for every $k$ (`conjecture1_eventual`), and in its pure form when every odd prime
  exponent of $k$ is at most $3$ (`conjecture1_of_exponent_le_three`);
- the same with the Carmichael function $\lambda$ in place of $\varphi$:
  $a(n + \lambda(k)) \equiv a(n) \pmod k$ under the same condition (`period_carmichael`), and
  eventually for every $k$ (`conjecture1_carmichael_eventual`). Here $\lambda(k) \mid
  \varphi(k)$. At $k = 8$ the period $\lambda(8) = 2$ cannot be replaced by $1$, as
  $a(1) \not\equiv a(0) \pmod 8$ (`carmichael_eight_sharp`);
- conjecture 2) and its integrality consequence (`conjecture2`, `conjecture2_exp_integral`);
- conjectures 3) and 4) for all $m, n \ge 1$ (`conjecture3`, `conjecture4`), with
  $v_2(m)$ written `m.factorization 2`.

In Lean, $\cos 2x$ is `rescale 2 (cos ℚ)` and $\lambda$ is `ArithmeticFunction.carmichael`.
Each congruence theorem also states that every
$a(n)$ is an integer: it provides an integer sequence `b` with `b n = a n` for all `n`. The
exponential of a series $L$ with zero constant term is `subst L (exp ℚ)`.

*References:*
- N. J. A. Sloane, [A000464](https://oeis.org/A000464); the conjectures are Peter Bala's
  comments of December 22, 2021.
- J. W. L. Glaisher, On the coefficients in the expansions of $\cos x / \cos 2x$ and
  $\sin x / \cos 2x$, Quart. J. Pure Appl. Math. 45 (1914), 187–222.
-/

@[expose] public section

namespace OeisA464

open PowerSeries

/-- OEIS A000464: $a(n) = (2n+1)!\,[x^{2n+1}]\, \sin x / \cos 2x$. -/
noncomputable def a (n : ℕ) : ℚ :=
  (2 * n + 1).factorial * coeff (2 * n + 1) (sin ℚ * (rescale (2 : ℚ) (cos ℚ))⁻¹)

/-- Bala's conjecture 1) is false as stated: it is not true that for every $k \ge 1$ the
sequence $(a(n))_{n \ge 1}$ modulo $k$ is purely periodic with a period dividing
$\varphi(k)$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000020"]
theorem not_conjecture1 :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ¬ ∀ k : ℕ, 1 ≤ k → ∃ T : ℕ, 0 < T ∧ T ∣ k.totient ∧
        ∀ n : ℕ, 1 ≤ n → b (n + T) ≡ b n [ZMOD k] := by
  sorry

/-- For every multiple $k$ of $81$, the sequence $(a(n))_{n \ge 1}$ modulo $k$ is not purely
periodic with any period $T \ge 1$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000020"]
theorem not_periodic_of_eighty_one_dvd :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ k T : ℕ, 81 ∣ k → 0 < T → ¬ ∀ n : ℕ, 1 ≤ n → b (n + T) ≡ b n [ZMOD k] := by
  sorry

/-- The counterexample: $a(1) = 11$ and $a(55) \equiv 65 \pmod{81}$. -/
@[category test, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000020"]
theorem a_fifty_five :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧ b 1 = 11 ∧ b 55 ≡ 65 [ZMOD 81] := by
  sorry

/-- The prime $2$: $a(n + 2^{e-1}) \equiv a(n) \pmod{2^e}$ for every $e \ge 1$ and every
$n \ge 0$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000020"]
theorem period_two_pow :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ e n : ℕ, 1 ≤ e → b (n + 2 ^ (e - 1)) ≡ b n [ZMOD 2 ^ e] := by
  sorry

/-- The prime $2$, sharper: $a(n + 2^{e-2}) \equiv a(n) \pmod{2^e}$ for every $e \ge 3$ and
every $n \ge 0$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000020"]
theorem period_two_pow_of_three_le :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ e n : ℕ, 3 ≤ e → b (n + 2 ^ (e - 2)) ≡ b n [ZMOD 2 ^ e] := by
  sorry

/-- Odd primes: $a(n + \frac{p-1}{2} p^{e-1}) \equiv (-1)^{(p-1)/2} a(n) \pmod{p^e}$ for every
odd prime $p$, every $e \ge 1$ and every $n$ with $2n + 1 \ge e$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000020"]
theorem antiperiod_odd_prime_pow :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ p e n : ℕ, p.Prime → p ≠ 2 → 1 ≤ e → e ≤ 2 * n + 1 →
        b (n + (p - 1) / 2 * p ^ (e - 1)) ≡ (-1) ^ ((p - 1) / 2) * b n [ZMOD p ^ e] := by
  sorry

/-- Odd primes: $a(n + \varphi(p^e)) \equiv a(n) \pmod{p^e}$ for every odd prime $p$, every
$e \ge 1$ and every $n$ with $2n + 1 \ge e$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000020"]
theorem period_odd_prime_pow :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ p e n : ℕ, p.Prime → p ≠ 2 → 1 ≤ e → e ≤ 2 * n + 1 →
        b (n + (p ^ e).totient) ≡ b n [ZMOD p ^ e] := by
  sorry

/-- Conjecture 1), corrected: $a(n + \varphi(k)) \equiv a(n) \pmod k$ for every $k \ge 1$ and
every $n$ such that $2n + 1$ is at least the exponent of each odd prime in $k$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000020"]
theorem period_totient :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ k n : ℕ, 1 ≤ k →
        (∀ p : ℕ, p.Prime → p ≠ 2 → k.factorization p ≤ 2 * n + 1) →
        b (n + k.totient) ≡ b n [ZMOD k] := by
  sorry

/-- Conjecture 1) in its eventual form: for every $k \ge 1$, the sequence $a(n)$ modulo $k$ is
eventually periodic with period dividing $\varphi(k)$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000020"]
theorem conjecture1_eventual :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n ≥ N, b (n + k.totient) ≡ b n [ZMOD k] := by
  sorry

/-- Conjecture 1) in its pure form when every odd prime exponent of $k$ is at most $3$:
then $a(n + \varphi(k)) \equiv a(n) \pmod k$ for all $n \ge 1$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000020"]
theorem conjecture1_of_exponent_le_three :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ k : ℕ, 1 ≤ k → (∀ p : ℕ, p.Prime → p ≠ 2 → k.factorization p ≤ 3) →
        ∀ n : ℕ, 1 ≤ n → b (n + k.totient) ≡ b n [ZMOD k] := by
  sorry

/-- Conjecture 1), corrected, with the Carmichael function: $a(n + \lambda(k)) \equiv a(n)
\pmod k$ for every $k \ge 1$ and every $n$ such that $2n + 1$ is at least the exponent of each
odd prime in $k$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000020"]
theorem period_carmichael :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ k n : ℕ, 1 ≤ k →
        (∀ p : ℕ, p.Prime → p ≠ 2 → k.factorization p ≤ 2 * n + 1) →
        b (n + ArithmeticFunction.carmichael k) ≡ b n [ZMOD k] := by
  sorry

/-- Conjecture 1) in its eventual form with the Carmichael function: for every $k \ge 1$, the
sequence $a(n)$ modulo $k$ is eventually periodic with period dividing $\lambda(k)$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000020"]
theorem conjecture1_carmichael_eventual :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n ≥ N,
        b (n + ArithmeticFunction.carmichael k) ≡ b n [ZMOD k] := by
  sorry

/-- The period $\lambda(8) = 2$ modulo $8$ cannot be replaced by $1$: $a(1) \not\equiv a(0)
\pmod 8$. -/
@[category test, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000020"]
theorem carmichael_eight_sharp :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ArithmeticFunction.carmichael 8 = 2 ∧ ¬ b 1 ≡ b 0 [ZMOD 8] := by
  sorry

/-- Bala's conjecture 2): for every shift $i \ge 0$, every prime $p$ and all $n, k \ge 1$,
$a(n p^k + i) \equiv a(n p^{k-1} + i) \pmod{p^k}$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000020"]
theorem conjecture2 :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ i p n k : ℕ, p.Prime → 1 ≤ n → 1 ≤ k →
        b (n * p ^ k + i) ≡ b (n * p ^ (k - 1) + i) [ZMOD p ^ k] := by
  sorry

/-- The consequence stated with conjecture 2): for every shift $i \ge 0$,
$\exp\left(\sum_{n \ge 1} a(n + i) x^n / n\right)$ has integer coefficients. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000020"]
theorem conjecture2_exp_integral (i N : ℕ) :
    ∃ z : ℤ, coeff N (subst (mk fun n : ℕ => if n = 0 then (0 : ℚ) else a (n + i) / n)
      (exp ℚ)) = z := by
  sorry

/-- Bala's conjecture 3): $a(mn) \equiv a(m)^n \pmod{2^{2 v_2(m) + 4}}$ for all $m, n \ge 1$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000020"]
theorem conjecture3 :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
        b (m * n) ≡ b m ^ n [ZMOD 2 ^ (2 * m.factorization 2 + 4)] := by
  sorry

/-- Bala's conjecture 4): for all $m, n \ge 1$, $a(2mn) \equiv a(n)^{2m}$ and
$a((2m+1)n) \equiv a(n)^{2m+1}$ modulo $2^{v_2(m) + 4}$. -/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-16-000020"]
theorem conjecture4 :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
        b (2 * m * n) ≡ b n ^ (2 * m) [ZMOD 2 ^ (m.factorization 2 + 4)] ∧
          b ((2 * m + 1) * n) ≡ b n ^ (2 * m + 1) [ZMOD 2 ^ (m.factorization 2 + 4)] := by
  sorry

end OeisA464

end
