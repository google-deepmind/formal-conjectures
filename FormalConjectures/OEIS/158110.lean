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
# Exponentials of $\sum_{n \ge 1} q^{n^m} x^n / n$

The sequence lists the coefficients of $\exp\left(\sum_{n \ge 1} 2^{n^3} x^n / n\right)$.
Paul D. Hanna conjectured that $\exp\left(\sum_{n \ge 1} q^{n^m} x^n / n\right)$ has integer
coefficients for all nonnegative integers $q$ and $m$. Sela Fried proved this [Fr25].

*References:*
- [A158110](https://oeis.org/A158110), Paul D. Hanna, 2009.
- [Fr25] Sela Fried, [Proof of a conjecture stated in A158110](https://oeis.org/A158110/a158110.pdf),
  2025.
- [Fr26] Sela Fried, [Further proofs of conjectures from the OEIS](https://arxiv.org/abs/2607.24832),
  arXiv:2607.24832, 2026.
-/

@[expose] public section

namespace OeisA158110

open PowerSeries

/-- The series $\sum_{n \ge 1} q^{n^m} x^n / n$ over $\mathbb{Q}$. The sum starts at $n = 1$,
so the exponent $n^m$ is at least $1$ and $0^0$ never occurs. -/
noncomputable def logSeries (q m : ℕ) : ℚ⟦X⟧ :=
  mk fun n => if n = 0 then 0 else (q : ℚ) ^ (n ^ m) / n

/-- The coefficients of $\exp\left(\sum_{n \ge 1} 2^{n^3} x^n / n\right)$, the sequence A158110.
`subst L (exp ℚ)` is the composition $\exp \circ L$. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n (subst (logSeries 2 3) (exp ℚ))

@[category test, AMS 5 11]
theorem a_0 : a 0 = 1 := by
  sorry

@[category test, AMS 5 11]
theorem a_1 : a 1 = 2 := by
  sorry

@[category test, AMS 5 11]
theorem a_2 : a 2 = 130 := by
  sorry

/--
"Conjecture: given q and m are nonnegative integers, then exp( Sum_{n>=1} q^(n^m)*x^n/n ) is a
power series in x with integer coefficients."
- Paul D. Hanna, Mar 19 2009.

Proved by Sela Fried [Fr25]. The case $m = 0$ gives $(1 - x)^{-q}$, and $q = 0$ gives $1$.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-14-000003"]
theorem conjecture (q m n : ℕ) : ∃ z : ℤ, coeff n (subst (logSeries q m) (exp ℚ)) = z := by
  sorry

end OeisA158110
