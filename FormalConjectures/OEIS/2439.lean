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
# OEIS A002439, Bala's conjectures for $\sin 2x / (2 \cos 3x)$

OEIS A002439 (Glaisher's $T$ numbers) is the expansion of the e.g.f. $\sin 2x / (2 \cos 3x)$.
Its terms are the odd-index coefficients, with offset $0$:
$a(n) = (2n+1)!\,[x^{2n+1}]\, \sin 2x / (2 \cos 3x)$, so $a = 1, 23, 1681, 257543, \dots$
(J. W. L. Glaisher, 1898–99). Peter Bala (OEIS, December 18, 2021) made these conjectures; the
file reads them for $m, n \ge 1$:
- 3)(i) $a(mn) \equiv a(m)^n \pmod{2^k}$ for $k = 2 v_2(m) + 7$;
- 3)(ii) $a(mn) \equiv a(m)^n \pmod{3^k}$ for $k = 2 v_3(m) + 2$;
- 4) $a(2mn) \equiv a(n)^{2m}$ and $a((2m+1)n) \equiv a(n)^{2m+1} \pmod{2^k}$ for
  $k = v_2(m) + 7$;
- 5) $a(3mn) \equiv a(n)^{3m}$ and $a((3m+1)n) \equiv a(n)^{3m+1} \pmod{3^k}$ for
  $k = v_3(m) + 2$, and $a((3m+2)n) \equiv a(n)^{3m+2} \pmod{9}$;
- 6) for every prime $p \ge 5$, with $h = (p-1)/2$:
  $a(hnm) \equiv a(hn)^m \pmod{p^k}$ for $k = v_p(m-1) + 1$.
On December 25, 2021 he added the formula $a(n) \equiv 23^n \pmod{1152}$, where
$1152 = 2^7 \cdot 3^2$.

The file states:
- conjectures 3), 4) and 5) for all $m, n \ge 1$ (`conjecture3_two`, `conjecture3_three`,
  `conjecture4`, `conjecture5`); the last clause of 5) has no $k$, and it is stated for all
  $m \ge 0$ (`conjecture5_iii`); the case $m = 0$ is $a(2n) \equiv a(n)^2 \pmod 9$;
- the congruence $a(n) \equiv 23^n \pmod{1152}$ for all $n \ge 0$ (`a_mod_1152`);
- conjecture 6) is false (`not_conjecture6`): for $p = 5$, $n = 1$, $m = 3126 = 1 + 5^5$ we
  have $k = 6$, but $a(6252) \equiv (1 + 5^5)\,a(2) \pmod{5^6}$ and
  $v_5(a(6252) - a(2)^{3126}) = 5$ (`conjecture6_counterexample`);
- the odd-prime congruence $a(n + h p^{e-1}) \equiv (-1)^h a(n) \pmod{p^e}$ for odd primes $p$,
  $h = (p-1)/2$, $e \ge 1$ and $2n + 1 \ge e$ (`antiperiod_odd_prime_pow`);
- conjecture 6) holds when $v_p(m-1) \le (p-1) n$ (`conjecture6_of_le`);
- for every prime $p \ge 5$, $e \ge 1$ and every $n \ge 0$,
  $a(n + h p^{e-1}) \equiv (-1)^h \big(1 - \chi_{12}(p)\, p^{2n+1}\big)\, a(n) \pmod{p^e}$, where
  $\chi_{12}(p) = 1$ for $p \equiv \pm 1 \pmod{12}$ and $\chi_{12}(p) = -1$ for
  $p \equiv \pm 5 \pmod{12}$ (`chi12`, `antiperiod_euler`);
- conjecture 6) holds exactly when $v_p(m-1) \le (p-1) n$ (`conjecture6_iff`);
- $a(n + 3^{e-1}) \equiv -a(n) \pmod{3^e}$ for every $e \ge 1$ and every $n$
  (`antiperiod_three`);
- 5)(i), (ii) hold modulo $3^{v_3(m) + 3}$ (`conjecture5_strong`).

In Lean, $\sin 2x$ is `rescale 2 (sin ℚ)` and $\cos 3x$ is `rescale 3 (cos ℚ)`. Here $v_p(m)$ is
written `m.factorization p`, so $v_p(0) = 0$ and the case $m = 1$ of 6) is the identity; the
valuation of an integer is `padicValInt`. Each congruence theorem also states that every
$a(n)$ is an integer: it provides an integer sequence `b` with `b n = a n` for all `n`.

*References:*
- N. J. A. Sloane, [A002439](https://oeis.org/A002439); the conjectures are Peter Bala's
  comments of December 18, 2021, and the formula is his comment of December 25, 2021.
- J. W. L. Glaisher, On a set of coefficients analogous to the Eulerian numbers, Proc. London
  Math. Soc. 31 (1899), 216–235.
-/

@[expose] public section

namespace OeisA2439

open PowerSeries

/-- OEIS A002439: $a(n) = (2n+1)!\,[x^{2n+1}]\, \sin 2x / (2 \cos 3x)$. -/
noncomputable def a (n : ℕ) : ℚ :=
  (2 * n + 1).factorial *
    coeff (2 * n + 1) (rescale (2 : ℚ) (sin ℚ) * (2 * rescale (3 : ℚ) (cos ℚ))⁻¹)

/-- The Dirichlet character $\chi_{12}$ at an integer $p$ prime to $6$: $\chi_{12}(p) = 1$ if
$p \equiv \pm 1 \pmod{12}$ and $\chi_{12}(p) = -1$ if $p \equiv \pm 5 \pmod{12}$. -/
def chi12 (p : ℕ) : ℤ := if p % 12 = 1 ∨ p % 12 = 11 then 1 else -1

/-- Bala's conjecture 3)(i): $a(mn) \equiv a(m)^n \pmod{2^{2 v_2(m) + 7}}$ for all
$m, n \ge 1$. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000002"]
theorem conjecture3_two :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
        b (m * n) ≡ b m ^ n [ZMOD 2 ^ (2 * m.factorization 2 + 7)] := by
  sorry

/-- Bala's conjecture 3)(ii): $a(mn) \equiv a(m)^n \pmod{3^{2 v_3(m) + 2}}$ for all
$m, n \ge 1$. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000002"]
theorem conjecture3_three :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
        b (m * n) ≡ b m ^ n [ZMOD 3 ^ (2 * m.factorization 3 + 2)] := by
  sorry

/-- Bala's conjecture 4): for all $m, n \ge 1$, $a(2mn) \equiv a(n)^{2m}$ and
$a((2m+1)n) \equiv a(n)^{2m+1}$ modulo $2^{v_2(m) + 7}$. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000002"]
theorem conjecture4 :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
        b (2 * m * n) ≡ b n ^ (2 * m) [ZMOD 2 ^ (m.factorization 2 + 7)] ∧
          b ((2 * m + 1) * n) ≡ b n ^ (2 * m + 1) [ZMOD 2 ^ (m.factorization 2 + 7)] := by
  sorry

/-- Bala's conjecture 5)(i), (ii): for all $m, n \ge 1$, $a(3mn) \equiv a(n)^{3m}$ and
$a((3m+1)n) \equiv a(n)^{3m+1}$ modulo $3^{v_3(m) + 2}$. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000002"]
theorem conjecture5 :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
        b (3 * m * n) ≡ b n ^ (3 * m) [ZMOD 3 ^ (m.factorization 3 + 2)] ∧
          b ((3 * m + 1) * n) ≡ b n ^ (3 * m + 1) [ZMOD 3 ^ (m.factorization 3 + 2)] := by
  sorry

/-- Bala's conjecture 5)(iii): $a((3m+2)n) \equiv a(n)^{3m+2} \pmod 9$ for all $m \ge 0$ and
$n \ge 1$. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000002"]
theorem conjecture5_iii :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ m n : ℕ, 1 ≤ n → b ((3 * m + 2) * n) ≡ b n ^ (3 * m + 2) [ZMOD 9] := by
  sorry

/-- Bala's congruence $a(n) \equiv 23^n \pmod{1152}$ for all $n \ge 0$. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000002"]
theorem a_mod_1152 :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧ ∀ n : ℕ, b n ≡ 23 ^ n [ZMOD 1152] := by
  sorry

/-- Bala's conjecture 6) is false: it is not true that for every prime $p \ge 5$ and all
$m, n \ge 1$, $a(hnm) \equiv a(hn)^m \pmod{p^{v_p(m-1) + 1}}$, where $h = (p-1)/2$. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000002"]
theorem not_conjecture6 :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ¬ ∀ p m n : ℕ, p.Prime → 5 ≤ p → 1 ≤ m → 1 ≤ n →
        b ((p - 1) / 2 * n * m) ≡ b ((p - 1) / 2 * n) ^ m
          [ZMOD p ^ ((m - 1).factorization p + 1)] := by
  sorry

/-- The counterexample to conjecture 6) at $p = 5$, $n = 1$, $m = 3126$: $a(2) = 1681$,
$a(6252) \equiv (1 + 5^5)\,a(2) \pmod{5^6}$, and $v_5(a(6252) - a(2)^{3126}) = 5$, while 6)
asks for $v_5 \ge v_5(3125) + 1 = 6$. -/
@[category test, AMS 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000002"]
theorem conjecture6_counterexample :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧ b 2 = 1681 ∧
      b 6252 ≡ (1 + 5 ^ 5) * b 2 [ZMOD 5 ^ 6] ∧ padicValInt 5 (b 6252 - b 2 ^ 3126) = 5 := by
  sorry

/-- Odd primes: $a(n + \frac{p-1}{2} p^{e-1}) \equiv (-1)^{(p-1)/2} a(n) \pmod{p^e}$ for every
odd prime $p$, every $e \ge 1$ and every $n$ with $2n + 1 \ge e$. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000002"]
theorem antiperiod_odd_prime_pow :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ p e n : ℕ, p.Prime → p ≠ 2 → 1 ≤ e → e ≤ 2 * n + 1 →
        b (n + (p - 1) / 2 * p ^ (e - 1)) ≡ (-1) ^ ((p - 1) / 2) * b n [ZMOD p ^ e] := by
  sorry

/-- Conjecture 6), corrected: for every prime $p \ge 5$ and all $m, n \ge 1$ with
$v_p(m-1) \le (p-1) n$, $a(hnm) \equiv a(hn)^m \pmod{p^{v_p(m-1) + 1}}$, where
$h = (p-1)/2$. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000002"]
theorem conjecture6_of_le :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ p m n : ℕ, p.Prime → 5 ≤ p → 1 ≤ m → 1 ≤ n → (m - 1).factorization p ≤ (p - 1) * n →
        b ((p - 1) / 2 * n * m) ≡ b ((p - 1) / 2 * n) ^ m
          [ZMOD p ^ ((m - 1).factorization p + 1)] := by
  sorry

/-- For every prime $p \ge 5$, with $h = (p-1)/2$, every $e \ge 1$ and every $n \ge 0$,
$a(n + h p^{e-1}) \equiv (-1)^h \big(1 - \chi_{12}(p)\, p^{2n+1}\big)\, a(n) \pmod{p^e}$. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000002"]
theorem antiperiod_euler :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ p e n : ℕ, p.Prime → 5 ≤ p → 1 ≤ e →
        b (n + (p - 1) / 2 * p ^ (e - 1)) ≡
          (-1) ^ ((p - 1) / 2) * (1 - chi12 p * (p : ℤ) ^ (2 * n + 1)) * b n [ZMOD p ^ e] := by
  sorry

/-- Conjecture 6), exactly: for every prime $p \ge 5$ and all $m, n \ge 1$, with
$h = (p-1)/2$, $a(hnm) \equiv a(hn)^m \pmod{p^{v_p(m-1) + 1}}$ holds if and only if
$v_p(m-1) \le (p-1) n$. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000002"]
theorem conjecture6_iff :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ p m n : ℕ, p.Prime → 5 ≤ p → 1 ≤ m → 1 ≤ n →
        (b ((p - 1) / 2 * n * m) ≡ b ((p - 1) / 2 * n) ^ m
          [ZMOD p ^ ((m - 1).factorization p + 1)] ↔ (m - 1).factorization p ≤ (p - 1) * n) := by
  sorry

/-- The prime $3$: $a(n + 3^{e-1}) \equiv -a(n) \pmod{3^e}$ for every $e \ge 1$ and every
$n \ge 0$. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000002"]
theorem antiperiod_three :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ e n : ℕ, 1 ≤ e → b (n + 3 ^ (e - 1)) ≡ -b n [ZMOD 3 ^ e] := by
  sorry

/-- Conjecture 5)(i), (ii) with one more power of $3$: for all $m, n \ge 1$,
$a(3mn) \equiv a(n)^{3m}$ and $a((3m+1)n) \equiv a(n)^{3m+1}$ modulo $3^{v_3(m) + 3}$. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000002"]
theorem conjecture5_strong :
    ∃ b : ℕ → ℤ, (∀ n, (b n : ℚ) = a n) ∧
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
        b (3 * m * n) ≡ b n ^ (3 * m) [ZMOD 3 ^ (m.factorization 3 + 3)] ∧
          b ((3 * m + 1) * n) ≡ b n ^ (3 * m + 1) [ZMOD 3 ^ (m.factorization 3 + 3)] := by
  sorry

end OeisA2439

end
