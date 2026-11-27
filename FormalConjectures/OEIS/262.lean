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
# Sets of lists

$a(n)$ is the number of partitions of $\{1, \ldots, n\}$ into any number of lists, where a list
is an ordered subset. Its e.g.f. is $\sum_{n \ge 0} a(n) x^n/n! = \exp(x/(1-x))$.

*References:*
- [A000262](https://oeis.org/A000262), N. J. A. Sloane.
- [Ba17] P. Bala, [Integer sequences that become periodic on reduction modulo k for all
  k](https://oeis.org/A047974/a047974_1.pdf), Dec 03 2017, Theorem 1.
-/

@[expose] public section

namespace OeisA262

open PowerSeries

/-- The rational e.g.f. $\sum a(n) x^n / n!$ of an integer sequence. -/
noncomputable def egf (a : ℕ → ℤ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => (a n : ℚ) / n.factorial

/-- $k \mid a(n + k) - a(n)$ for every $k \ge 2$ and every $n$. -/
def PeriodicModAll (a : ℕ → ℤ) : Prop :=
  ∀ n k : ℕ, 2 ≤ k → a (n + k) ≡ a n [ZMOD k]

@[category test, AMS 11]
theorem a_0 (a : ℕ → ℤ) (h : egf a = (exp ℚ).subst (X * (1 - X)⁻¹)) : a 0 = 1 := by
  sorry

@[category test, AMS 11]
theorem a_1 (a : ℕ → ℤ) (h : egf a = (exp ℚ).subst (X * (1 - X)⁻¹)) : a 1 = 1 := by
  sorry

@[category test, AMS 11]
theorem a_2 (a : ℕ → ℤ) (h : egf a = (exp ℚ).subst (X * (1 - X)⁻¹)) : a 2 = 3 := by
  sorry

@[category test, AMS 11]
theorem a_3 (a : ℕ → ℤ) (h : egf a = (exp ℚ).subst (X * (1 - X)⁻¹)) : a 3 = 13 := by
  sorry

@[category test, AMS 11]
theorem a_4 (a : ℕ → ℤ) (h : egf a = (exp ℚ).subst (X * (1 - X)⁻¹)) : a 4 = 73 := by
  sorry

/--
Bala's Theorem 1 [Ba17]: if $\sum a(n) x^n/n! = F(x)\exp(x G(x))$ with $F, G \in \mathbb{Z}[[x]]$
and $G(0) = 1$, then $a(n + k) \equiv a(n) \pmod k$ for all $n$ and $k$.

Formal proof by Wentao Li, with AI assistance. It follows Bala's recurrence argument [Ba17].
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-14-000009"]
theorem bala_theorem1 :
    ∀ F G : ℤ⟦X⟧, constantCoeff G = 1 → ∀ a : ℕ → ℤ,
      egf a = map (Int.castRingHom ℚ) F * (exp ℚ).subst (X * map (Int.castRingHom ℚ) G) →
        ∀ n k : ℕ, a (n + k) ≡ a n [ZMOD k] := by
  sorry

/--
"We conjecture that for k = 2,3,4,..., the difference a(n+k) - a(n) is divisible by k: if true,
then for each k the sequence a(n) taken modulo k is periodic with period dividing k."
- Peter Bala, Nov 14 2017.

The theorem states that $\exp(x/(1-x))$ has a unique integer coefficient sequence and that this
sequence satisfies the conjecture. Bala proved the conjecture [Ba17]. Formal proof by Wentao Li,
with AI assistance, from Bala's Theorem 1 with $F = 1$ and $G = 1/(1-x)$. Ahaan Kallat gave an
independent Lean proof of the congruence by a different route, in
[ahaankallat/congruence-phenomena-higher-order-lean](https://github.com/ahaankallat/congruence-phenomena-higher-order-lean/tree/8ca3c4250c58f47eadabd82bcd5650f3d0632d7b).
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-14-000009"]
theorem conjecture :
    (∃! a : ℕ → ℤ, egf a = (exp ℚ).subst (X * (1 - X)⁻¹)) ∧
      ∀ a : ℕ → ℤ, egf a = (exp ℚ).subst (X * (1 - X)⁻¹) → PeriodicModAll a := by
  sorry

end OeisA262
