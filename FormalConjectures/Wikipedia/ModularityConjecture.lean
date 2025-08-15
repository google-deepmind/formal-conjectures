/-
Copyright 2025 The Formal Conjectures Authors.

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

import FormalConjectures.Util.ProblemImports

/-!
# Modularity conjecture

The **Modularity conjecture** (also know as the Shimura--Taniyama--Weil conjecture) states that
every rational elliptic curve is modular, meaning that it can be
associated with a modular form. We state the `a_p` version of the conjecture, which relates the
coefficients of the modular form to the number of points on the elliptic curve over finite fields.

Since we don't have the conductor of the elliptic curve, our definition of `a_p(E)` differs from
that in the literature at primes of bad reduction. For this reason, we state the conjecture with the
assumption that `p ∤ N`, in order to give an equivalent statement.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Modularity_theorem)
- [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005]

-/


open Complex CongruenceSubgroup ModularFormClass
open scoped UpperHalfPlane Real ModularForm CongruenceSubgroup

noncomputable section

/-- The `n`-th Fourier coefficient of a modular forms (around the cusp at infinity). -/
def modularFormAn (n : ℕ) {N : ℕ} {k : ℤ} (f : CuspForm (Gamma0 N) k) : ℂ :=
  (qExpansion N f).coeff ℂ n

local notation:73 "a_[" n:0 "]" f:72 => modularFormAn n f

/-- We need to reduce a rational modulo `p`, in practice we wont be dividing by zero since the
conductor of the elliptic curve saves us.-/
def ratRed (q : ℚ) (p : ℕ) : ZMod p :=
  (q.num : ZMod p) * (q.den : ZMod p)⁻¹

/-- The set of points on an elliptic curve over `ZMod n`. -/
def setOfPointsModN (E : WeierstrassCurve ℚ) [E.IsElliptic] (n : ℕ) :=
  {P : ZMod n × ZMod n |
    let ⟨x, y⟩ := P
    y ^ 2 + ratRed E.a₁ n * x * y + ratRed E.a₃ n * y =
      x ^ 3 + ratRed E.a₂ n * x ^ 2 + ratRed E.a₄ n * x + ratRed E.a₆ n}

/-- The set of point `mod n` is finite.-/
instance apFintype (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ+) :
    Fintype (setOfPointsModN E p) := by
  rw [setOfPointsModN]
  apply Subtype.fintype _

/-- Note that normally this is written as `p + 1 - #E(𝔽ₚ)`, but since we don't have a point at
infinty on this affine curve we only have `p` -/
def WeierstrassCurve.ap (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) : ℕ :=
  p - Cardinal.toNat (Cardinal.mk (setOfPointsModN E p))

/-- Since we don't have Hecke operators yet, we define this via the q-expansion coefficients. See
 Proposition 5.8.5 of [diamondshurman2005]. -/
def IsNormalisedEigenform {N : ℕ} {k : ℤ} (f : CuspForm (Gamma0 N) k) : Prop :=
  a_[1]f = 1 ∧
  (∀ (m n : ℕ), m.Coprime n → a_[n * m]f = a_[n]f * a_[m]f) ∧
  (∀ (p r : ℕ), p.Prime → 2 ≤ r → (N : ZMod p) ≠ 0 →
    a_[p ^ r]f = a_[p]f * a_[p ^ (r - 1)]f - p ^ (k - 1) * a_[p ^ (r - 2)]f) ∧
  ∀ (p r : ℕ), p.Prime → 2 ≤ r → (N : ZMod p) = 0 → a_[p ^ r]f = (a_[p]f) ^ r

/-- See  theorem 8.8.1 of [diamondshurman2005]. -/
def ModularityConjecture (E : WeierstrassCurve ℚ) [E.IsElliptic] : Prop :=
  ∃ (N : ℕ+) (f : CuspForm (Gamma0 N) 2), IsNormalisedEigenform f ∧
    ∀ (p : ℕ), p.Prime → (N : ZMod p) ≠ 0 → a_[p]f = E.ap p

@[category research solved, AMS 11]
theorem modularity_conjecture (E : WeierstrassCurve ℚ) [E.IsElliptic] : ModularityConjecture E := by
  sorry
