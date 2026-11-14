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
# $\exp(x/(1-x))$ and $\exp(x/(1-x)^2)$ modulo $k$

Peter Bala conjectured that the e.g.f. coefficients $a(n)$ of $\exp(x/(1-x))$ (A000262) and of
$\exp(x/(1-x)^2)$ (A082579) satisfy $k \mid a(n+k) - a(n)$ for all $n$ and all $k \ge 2$, and proved
it in his note: if $\sum a(n) x^n/n! = F(x)\exp(x G(x))$ with $F, G \in \mathbb{Z}[[x]]$ and $G(0) =
1$, then $a(n + k) \equiv a(n) \pmod k$.

*References:*
- [A000262](https://oeis.org/A000262) and [A082579](https://oeis.org/A082579): conjecture by Peter
  Bala, Nov 14 2017; proved by him, Jan 20 2018.
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

/--
Bala's Theorem 1 [Ba17]: if $\sum a(n) x^n/n! = F(x)\exp(x G(x))$ with $F, G \in \mathbb{Z}[[x]]$
and $G(0) = 1$, then $a(n + k) \equiv a(n) \pmod k$ for all $n$ and $k$.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-14-000009"]
theorem bala_theorem1 :
    ∀ F G : ℤ⟦X⟧, constantCoeff G = 1 → ∀ a : ℕ → ℤ,
      egf a = map (Int.castRingHom ℚ) F * (exp ℚ).subst (X * map (Int.castRingHom ℚ) G) →
        ∀ n k : ℕ, a (n + k) ≡ a n [ZMOD k] := by
  sorry

/--
"We conjecture that for k = 2,3,4,..., the difference a(n+k) - a(n) is divisible by k." - Peter
Bala, Nov 14 2017; "The above conjecture is true." - Peter Bala, Jan 20 2018 (A000262).

The e.g.f. $\exp(x/(1-x))$ has a unique integer coefficient sequence, and it satisfies the claim.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-14-000009"]
theorem a000262 :
    (∃! a : ℕ → ℤ, egf a = (exp ℚ).subst (X * (1 - X)⁻¹)) ∧
      ∀ a : ℕ → ℤ, egf a = (exp ℚ).subst (X * (1 - X)⁻¹) → PeriodicModAll a := by
  sorry

/--
The same claim for A082579, with e.g.f. $\exp(x/(1-x)^2)$ (Peter Bala, 2017–2018).
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-14-000009"]
theorem a082579 :
    (∃! a : ℕ → ℤ, egf a = (exp ℚ).subst (X * ((1 - X) ^ 2)⁻¹)) ∧
      ∀ a : ℕ → ℤ, egf a = (exp ℚ).subst (X * ((1 - X) ^ 2)⁻¹) → PeriodicModAll a := by
  sorry

end OeisA262
