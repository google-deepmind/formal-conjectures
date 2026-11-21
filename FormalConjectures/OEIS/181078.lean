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
# Hanna's exponential series for $\binom{n+k-1}{k}^{n+k-1}$

The sequence lists the coefficients of
$$\exp\Bigl(\sum_{n \ge 1} \Bigl[\sum_{k \ge 0} \binom{n+k-1}{k}^{n+k-1} x^k\Bigr]
  \frac{x^n}{n}\Bigr).$$

*References:*
- [A181078](https://oeis.org/A181078), Paul D. Hanna, 2010.
-/

@[expose] public section

namespace OeisA181078

open PowerSeries

/-- The series $\sum_{n \ge 1} \bigl[\sum_{k \ge 0} f(n,k)\,x^k\bigr] \frac{x^n}{n}$ over
$\mathbb{Q}$. Its coefficient of $x^m$ is $\sum_{n=1}^{m} f(n, m-n)/n$. -/
noncomputable def hannaLog (f : ℕ → ℕ → ℤ) : ℚ⟦X⟧ :=
  mk fun m => ∑ n ∈ Finset.Icc 1 m, (f n (m - n) : ℚ) / n

/-- The series $\exp\Bigl(\sum_{n \ge 1} \bigl[\sum_{k \ge 0} f(n,k)\,x^k\bigr]
\frac{x^n}{n}\Bigr)$ over $\mathbb{Q}$. -/
noncomputable def hannaExp (f : ℕ → ℕ → ℤ) : ℚ⟦X⟧ := subst (hannaLog f) (exp ℚ)

/-- The coefficients of
$\exp\bigl(\sum_{n \ge 1} [\sum_{k \ge 0} \binom{n+k-1}{k}^{n+k-1} x^k] x^n/n\bigr)$. -/
noncomputable def a (m : ℕ) : ℚ :=
  coeff m (hannaExp fun n k => ((n + k - 1).choose k : ℤ) ^ (n + k - 1))

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
theorem a_4 : a 4 = 29 := by
  sorry

/--
"Conjecture: this sequence consists entirely of integers."
- Paul D. Hanna, Oct 03 2010.

Proved in Lean in
[the-omega-institute/trureturing](https://github.com/the-omega-institute/trureturing/blob/ea2976219e3a793b0f41944d2c4a9fd11f15ec47/D5/S1/Recurrence/Algebraic/HannaA181078Integrality.lean)
on November 13, 2026. The linked formal proof is an independent proof by Wentao Li, with AI
assistance.
-/
@[category research solved, AMS 5 11 13, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-17-000018"]
theorem conjecture (m : ℕ) : ∃ z : ℤ, a m = z := by
  sorry

end OeisA181078

end
