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
# Expansion of $\exp(x/(1-x)^2)$

The sequence lists the e.g.f. coefficients of $\exp(x/(1-x)^2)$: $\sum_{n \ge 0} a(n) x^n/n! =
\exp(x/(1-x)^2)$.

*References:*
- [A082579](https://oeis.org/A082579), Emanuele Munarini, 2003.
- [Ba17] P. Bala, [Integer sequences that become periodic on reduction modulo k for all
  k](https://oeis.org/A047974/a047974_1.pdf), Dec 03 2017, Theorem 1.
-/

@[expose] public section

namespace OeisA82579

open PowerSeries

/-- The rational e.g.f. $\sum a(n) x^n / n!$ of an integer sequence. -/
noncomputable def egf (a : ℕ → ℤ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => (a n : ℚ) / n.factorial

/-- $k \mid a(n + k) - a(n)$ for every $k \ge 2$ and every $n$. -/
def PeriodicModAll (a : ℕ → ℤ) : Prop :=
  ∀ n k : ℕ, 2 ≤ k → a (n + k) ≡ a n [ZMOD k]

@[category test, AMS 11]
theorem a_0 (a : ℕ → ℤ) (h : egf a = (exp ℚ).subst (X * ((1 - X) ^ 2)⁻¹)) : a 0 = 1 := by
  sorry

@[category test, AMS 11]
theorem a_1 (a : ℕ → ℤ) (h : egf a = (exp ℚ).subst (X * ((1 - X) ^ 2)⁻¹)) : a 1 = 1 := by
  sorry

@[category test, AMS 11]
theorem a_2 (a : ℕ → ℤ) (h : egf a = (exp ℚ).subst (X * ((1 - X) ^ 2)⁻¹)) : a 2 = 5 := by
  sorry

@[category test, AMS 11]
theorem a_3 (a : ℕ → ℤ) (h : egf a = (exp ℚ).subst (X * ((1 - X) ^ 2)⁻¹)) : a 3 = 31 := by
  sorry

@[category test, AMS 11]
theorem a_4 (a : ℕ → ℤ) (h : egf a = (exp ℚ).subst (X * ((1 - X) ^ 2)⁻¹)) : a 4 = 241 := by
  sorry

/--
"More generally, we conjecture that for k = 2,3,4,... the difference a(n+k) - a(n) is divisible
by k: if true, then for each k the sequence a(n) taken modulo k would be periodic with period
dividing k."
- Peter Bala, Nov 14 2017.

The theorem states that $\exp(x/(1-x)^2)$ has a unique integer coefficient sequence and that this
sequence satisfies the conjecture. Bala proved the conjecture [Ba17]. Formal proof by Wentao Li,
with AI assistance, from Bala's Theorem 1 with $F = 1$ and $G = 1/(1-x)^2$. Ahaan Kallat gave an
independent Lean proof of the congruence by a different route, in
[ahaankallat/congruence-phenomena-higher-order-lean](https://github.com/ahaankallat/congruence-phenomena-higher-order-lean/tree/8ca3c4250c58f47eadabd82bcd5650f3d0632d7b).
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-14-000009"]
theorem conjecture :
    (∃! a : ℕ → ℤ, egf a = (exp ℚ).subst (X * ((1 - X) ^ 2)⁻¹)) ∧
      ∀ a : ℕ → ℤ, egf a = (exp ℚ).subst (X * ((1 - X) ^ 2)⁻¹) → PeriodicModAll a := by
  sorry

end OeisA82579
