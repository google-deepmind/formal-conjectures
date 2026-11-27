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
# Hanna's exponential series for $\binom{n+k-1}{k}^{k^2+k}$

The sequence lists the coefficients of
$$\exp\Bigl(\sum_{n \ge 1} \Bigl[\sum_{k \ge 0} \binom{n+k-1}{k}^{k^2+k} x^k\Bigr]
  \frac{x^n}{n}\Bigr).$$

*References:*
- [A183129](https://oeis.org/A183129), Paul D. Hanna, 2010.
-/

@[expose] public section

namespace OeisA183129

open PowerSeries

/-- The series $\sum_{n \ge 1} \bigl[\sum_{k \ge 0} f(n,k)\,x^k\bigr] \frac{x^n}{n}$ over
$\mathbb{Q}$. Its coefficient of $x^m$ is $\sum_{n=1}^{m} f(n, m-n)/n$. -/
noncomputable def hannaLog (f : ℕ → ℕ → ℤ) : ℚ⟦X⟧ :=
  mk fun m => ∑ n ∈ Finset.Icc 1 m, (f n (m - n) : ℚ) / n

/-- The series $\exp\Bigl(\sum_{n \ge 1} \bigl[\sum_{k \ge 0} f(n,k)\,x^k\bigr]
\frac{x^n}{n}\Bigr)$ over $\mathbb{Q}$. -/
noncomputable def hannaExp (f : ℕ → ℕ → ℤ) : ℚ⟦X⟧ := subst (hannaLog f) (exp ℚ)

/-- The coefficients of
$\exp\bigl(\sum_{n \ge 1} [\sum_{k \ge 0} \binom{n+k-1}{k}^{k^2+k} x^k] x^n/n\bigr)$. -/
noncomputable def a (m : ℕ) : ℚ :=
  coeff m (hannaExp fun n k => ((n + k - 1).choose k : ℤ) ^ (k ^ 2 + k))

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by
  sorry

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  sorry

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by
  sorry

@[category test, AMS 11]
theorem a_3 : a 3 = 5 := by
  sorry

@[category test, AMS 11]
theorem a_4 : a 4 = 374 := by
  sorry

/--
"Conjecture: this sequence consists entirely of integers."
- Paul D. Hanna, Dec 25 2010.

Proved by Wentao Li, with AI assistance, by checking Dold's integrality congruences along
the rays $(n, k) \to (pn, pk)$. This pairing of terms is from trureturing issues
[#22220](https://github.com/the-omega-institute/trureturing/issues/22220),
[#22221](https://github.com/the-omega-institute/trureturing/issues/22221) and
[#22222](https://github.com/the-omega-institute/trureturing/issues/22222).
-/
@[category research solved, AMS 5 11 13, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000018"]
theorem conjecture (m : ℕ) : ∃ z : ℤ, a m = z := by
  sorry

/--
"Note that the following g.f. does NOT yield an integer series:
exp( Sum_{n>=1} [Sum_{k>=0} C(n+k-1,k)^(k^2+k-1) * x^k] * x^n/n )."
- Paul D. Hanna, Dec 25 2010.

The coefficient of $x^6$ is $19140157244799/2$. In Lean, `k ^ 2 + k - 1` is $0$ at
$k = 0$, where the source has $-1$; both give the term $1$, because
$\binom{n-1}{0} = 1$. Formal proof by Wentao Li, with AI assistance.
-/
@[category test, AMS 5 11 13, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000018"]
theorem note_not_integral :
    ¬∀ m, ∃ z : ℤ,
      coeff m (hannaExp fun n k => ((n + k - 1).choose k : ℤ) ^ (k ^ 2 + k - 1)) = z := by
  sorry

end OeisA183129

end
