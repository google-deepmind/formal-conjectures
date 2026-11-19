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
# OEIS A183128 and A183129, Hanna's binomial-power exponentials

For $f : \mathbb{N} \times \mathbb{N} \to \mathbb{Z}$, Paul D. Hanna's series have the form
$$\exp\Bigl(\sum_{n \ge 1} \Bigl[\sum_{k \ge 0} f(n,k)\,x^k\Bigr] \frac{x^n}{n}\Bigr).$$
The coefficient of $x^m$ in the logarithm is $\sum_{n=1}^{m} f(n, m-n)/n$. `hannaLog f` is the
power series over $\mathbb{Q}$ with these coefficients, and `hannaExp f` is its exponential.

Hanna (2010) conjectured that the following series have integer coefficients ("Conjecture: this
sequence consists entirely of integers"). Each entry defines its sequence (offset 0) as the
coefficients of the series.

| Entry | $f(n,k)$ | inner sum |
| --- | --- | --- |
| A183128 | $\binom{n+k-1}{k}^{k^2+1}$ | $k \ge 0$ |
| A183129 | $\binom{n+k-1}{k}^{k^2+k}$ | $k \ge 0$ |
| A181076 | $\binom{n+k-1}{k}^{n}$ | $k \ge 0$ |
| A181078 | $\binom{n+k-1}{k}^{n+k-1}$ | $k \ge 0$ |
| A181082 | $\binom{n}{k}^{n+k}$ | $0 \le k \le n$ |
| A181084 | $\binom{n}{k}^{n+k+1}$ | $0 \le k \le n$ |

He also notes that three related series do NOT have integer coefficients: the exponent $k^2$
(in A183128), the exponent $k^2+k-1$ (in A183129), and $\binom{n}{k}^{k}$ for $0 \le k \le n$
(in A181070). In Lean, `k ^ 2 + k - 1` is $0$ at $k = 0$, where the source has $-1$; both give
the term $1$, because $\binom{n-1}{0} = 1$.

Integer coefficients are stated as `∃ z : ℤ, coeff m F = z`, and $\exp$ of a series $L$ with zero
constant term as `subst L (exp ℚ)`.

*References:*
- Paul D. Hanna, [A183128](https://oeis.org/A183128) and [A183129](https://oeis.org/A183129),
  2010.
- Paul D. Hanna, [A181076](https://oeis.org/A181076), [A181078](https://oeis.org/A181078),
  [A181082](https://oeis.org/A181082), [A181084](https://oeis.org/A181084) and
  [A181070](https://oeis.org/A181070), 2010.
-/

@[expose] public section

namespace OeisA183128

open PowerSeries

/-- Hanna's logarithm $\sum_{n \ge 1} \bigl[\sum_{k \ge 0} f(n,k)\,x^k\bigr] \frac{x^n}{n}$ over
$\mathbb{Q}$: its coefficient of $x^m$ is $\sum_{n=1}^{m} f(n, m-n)/n$. -/
noncomputable def hannaLog (f : ℕ → ℕ → ℤ) : ℚ⟦X⟧ :=
  mk fun m => ∑ n ∈ Finset.Icc 1 m, (f n (m - n) : ℚ) / n

/-- Hanna's series $\exp\Bigl(\sum_{n \ge 1} \bigl[\sum_{k \ge 0} f(n,k)\,x^k\bigr]
\frac{x^n}{n}\Bigr)$ over $\mathbb{Q}$. -/
noncomputable def hannaExp (f : ℕ → ℕ → ℤ) : ℚ⟦X⟧ := subst (hannaLog f) (exp ℚ)

/-- OEIS A183128: the coefficients of
$\exp\bigl(\sum_{n \ge 1} [\sum_{k \ge 0} \binom{n+k-1}{k}^{k^2+1} x^k] x^n/n\bigr)$. -/
noncomputable def a183128 (m : ℕ) : ℚ :=
  coeff m (hannaExp fun n k => ((n + k - 1).choose k : ℤ) ^ (k ^ 2 + 1))

/-- OEIS A183129: the coefficients of
$\exp\bigl(\sum_{n \ge 1} [\sum_{k \ge 0} \binom{n+k-1}{k}^{k^2+k} x^k] x^n/n\bigr)$. -/
noncomputable def a183129 (m : ℕ) : ℚ :=
  coeff m (hannaExp fun n k => ((n + k - 1).choose k : ℤ) ^ (k ^ 2 + k))

/-- OEIS A181076: the coefficients of
$\exp\bigl(\sum_{n \ge 1} [\sum_{k \ge 0} \binom{n+k-1}{k}^{n} x^k] x^n/n\bigr)$. -/
noncomputable def a181076 (m : ℕ) : ℚ :=
  coeff m (hannaExp fun n k => ((n + k - 1).choose k : ℤ) ^ n)

/-- OEIS A181078: the coefficients of
$\exp\bigl(\sum_{n \ge 1} [\sum_{k \ge 0} \binom{n+k-1}{k}^{n+k-1} x^k] x^n/n\bigr)$. -/
noncomputable def a181078 (m : ℕ) : ℚ :=
  coeff m (hannaExp fun n k => ((n + k - 1).choose k : ℤ) ^ (n + k - 1))

/-- OEIS A181082: the coefficients of
$\exp\bigl(\sum_{n \ge 1} [\sum_{k=0}^{n} \binom{n}{k}^{n+k} x^k] x^n/n\bigr)$. -/
noncomputable def a181082 (m : ℕ) : ℚ :=
  coeff m (hannaExp fun n k => if k ≤ n then (n.choose k : ℤ) ^ (n + k) else 0)

/-- OEIS A181084: the coefficients of
$\exp\bigl(\sum_{n \ge 1} [\sum_{k=0}^{n} \binom{n}{k}^{n+k+1} x^k] x^n/n\bigr)$. -/
noncomputable def a181084 (m : ℕ) : ℚ :=
  coeff m (hannaExp fun n k => if k ≤ n then (n.choose k : ℤ) ^ (n + k + 1) else 0)

/-- **Hanna's conjecture in A183128.** Every term of A183128 is an integer. -/
@[category research solved, AMS 5 11 13, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000018"]
theorem a183128_integral (m : ℕ) : ∃ z : ℤ, a183128 m = z := by
  sorry

/-- **Hanna's conjecture in A183129.** Every term of A183129 is an integer. -/
@[category research solved, AMS 5 11 13, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000018"]
theorem a183129_integral (m : ℕ) : ∃ z : ℤ, a183129 m = z := by
  sorry

/-- **Hanna's note in A183128.** The series
$\exp\bigl(\sum_{n \ge 1} [\sum_{k \ge 0} \binom{n+k-1}{k}^{k^2} x^k] x^n/n\bigr)$ does not have
integer coefficients. -/
@[category test, AMS 5 11 13, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000018"]
theorem a183128_note :
    ¬∀ m, ∃ z : ℤ, coeff m (hannaExp fun n k => ((n + k - 1).choose k : ℤ) ^ (k ^ 2)) = z := by
  sorry

/-- **Hanna's note in A183129.** The series
$\exp\bigl(\sum_{n \ge 1} [\sum_{k \ge 0} \binom{n+k-1}{k}^{k^2+k-1} x^k] x^n/n\bigr)$ does not
have integer coefficients. -/
@[category test, AMS 5 11 13, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000018"]
theorem a183129_note :
    ¬∀ m, ∃ z : ℤ,
      coeff m (hannaExp fun n k => ((n + k - 1).choose k : ℤ) ^ (k ^ 2 + k - 1)) = z := by
  sorry

/-- **Hanna's note in A181070.** The series
$\exp\bigl(\sum_{n \ge 1} [\sum_{k=0}^{n} \binom{n}{k}^{k} x^k] x^n/n\bigr)$ does not have
integer coefficients. -/
@[category test, AMS 5 11 13, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000018"]
theorem a181070_note :
    ¬∀ m, ∃ z : ℤ,
      coeff m (hannaExp fun n k => if k ≤ n then (n.choose k : ℤ) ^ k else 0) = z := by
  sorry

/-- **Hanna's conjecture in A181076.** Every term of A181076 is an integer. -/
@[category research solved, AMS 5 11 13, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000018"]
theorem a181076_integral (m : ℕ) : ∃ z : ℤ, a181076 m = z := by
  sorry

/-- **Hanna's conjecture in A181078.** Every term of A181078 is an integer. -/
@[category research solved, AMS 5 11 13, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000018"]
theorem a181078_integral (m : ℕ) : ∃ z : ℤ, a181078 m = z := by
  sorry

/-- **Hanna's conjecture in A181082.** Every term of A181082 is an integer. -/
@[category research solved, AMS 5 11 13, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000018"]
theorem a181082_integral (m : ℕ) : ∃ z : ℤ, a181082 m = z := by
  sorry

/-- **Hanna's conjecture in A181084.** Every term of A181084 is an integer. -/
@[category research solved, AMS 5 11 13, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000018"]
theorem a181084_integral (m : ℕ) : ∃ z : ℤ, a181084 m = z := by
  sorry

end OeisA183128

end
