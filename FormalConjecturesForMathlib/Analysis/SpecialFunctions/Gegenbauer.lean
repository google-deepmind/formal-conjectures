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

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Gegenbauer (ultraspherical) polynomials

The Gegenbauer (or ultraspherical) polynomials `C_n^{(a)}` are the family of orthogonal
polynomials with respect to the weight `(1 - x²)^{a - 1/2}` on `[-1, 1]`. They generalise
both the Legendre polynomials (`a = 1/2`) and the Chebyshev polynomials of the second kind
(`a = 1`), and arise as the partial-wave / angular basis for scattering in `D` spacetime
dimensions, with parameter `a = (D - 3) / 2`.

We define them over an arbitrary field by the standard three-term recurrence
$$ C_0^{(a)} = 1, \qquad C_1^{(a)} = 2 a X, $$
$$ n\, C_n^{(a)} = 2 (n + a - 1)\, X\, C_{n-1}^{(a)} - (n + 2a - 2)\, C_{n-2}^{(a)} \quad (n \ge 2). $$
-/

open Polynomial

namespace Polynomial

variable {K : Type*} [Field K]

/--
The Gegenbauer (ultraspherical) polynomial `C_n^{(a)} : K[X]` with parameter `a : K`,
defined by the three-term recurrence
`C_0 = 1`, `C_1 = 2 a X`, and
`(n + 2) C_{n+2} = 2 (n + 1 + a) X C_{n+1} - (n + 2 a) C_n`.
-/
noncomputable def gegenbauer (a : K) : ℕ → K[X]
  | 0 => 1
  | 1 => C (2 * a) * X
  | (n + 2) => C ((n : K) + 2)⁻¹ *
      (C (2 * ((n : K) + 1 + a)) * X * gegenbauer a (n + 1)
        - C ((n : K) + 2 * a) * gegenbauer a n)

@[simp]
theorem gegenbauer_zero (a : K) : gegenbauer a 0 = 1 := rfl

@[simp]
theorem gegenbauer_one (a : K) : gegenbauer a 1 = C (2 * a) * X := rfl

/-- The defining three-term recurrence, valid for all `n`. -/
theorem gegenbauer_add_two (a : K) (n : ℕ) :
    gegenbauer a (n + 2) = C ((n : K) + 2)⁻¹ *
      (C (2 * ((n : K) + 1 + a)) * X * gegenbauer a (n + 1)
        - C ((n : K) + 2 * a) * gegenbauer a n) := rfl

/-- Closed form `C_2^{(a)} = 2 a (a + 1) X² - a`. -/
theorem gegenbauer_two [CharZero K] (a : K) :
    gegenbauer a 2 = C (2 * a * (a + 1)) * X ^ 2 - C a := by
  have h2 : (2 : K) ≠ 0 := by norm_num
  rw [gegenbauer_add_two, gegenbauer_one, gegenbauer_zero]
  simp only [Nat.cast_zero, zero_add, mul_one]
  rw [mul_sub,
    show C (2 * (1 + a)) * X * (C (2 * a) * X) = C (2 * (1 + a) * (2 * a)) * X ^ 2 by
      simp only [C_mul]; ring,
    ← mul_assoc, ← C_mul, ← C_mul,
    show (2 : K)⁻¹ * (2 * (1 + a) * (2 * a)) = 2 * a * (a + 1) by field_simp; ring,
    show (2 : K)⁻¹ * (2 * a) = a by field_simp]

/--
For `0 < a`, the Gegenbauer polynomial `C_n^{(a)}` has degree exactly `n` and positive leading
coefficient. Consequently `{C_0^{(a)}, …, C_{m-1}^{(a)}}` is a basis of the polynomials of degree
`< m`, so the Gegenbauer expansion of any such polynomial is unique.
-/
theorem gegenbauer_natDegree_leadingCoeff {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {a : K} (ha : 0 < a) :
    ∀ n, (gegenbauer a n).natDegree = n ∧ 0 < (gegenbauer a n).leadingCoeff
  | 0 => by constructor <;> simp [gegenbauer_zero]
  | 1 => by
    rw [gegenbauer_one]
    exact ⟨natDegree_C_mul_X _ (by positivity), by rw [leadingCoeff_C_mul_X]; positivity⟩
  | (n + 2) => by
    obtain ⟨hd1, hl1⟩ := gegenbauer_natDegree_leadingCoeff ha (n + 1)
    obtain ⟨hd0, hl0⟩ := gegenbauer_natDegree_leadingCoeff ha n
    have hd : (2 : K) * ((n : K) + 1 + a) ≠ 0 := by positivity
    set t1 : K[X] := C (2 * ((n : K) + 1 + a)) * X * gegenbauer a (n + 1) with ht1
    set t2 : K[X] := C ((n : K) + 2 * a) * gegenbauer a n with ht2
    have hlcprod : (C (2 * ((n : K) + 1 + a)) * X).leadingCoeff *
        (gegenbauer a (n + 1)).leadingCoeff ≠ 0 := by
      rw [leadingCoeff_C_mul_X]; exact mul_ne_zero hd hl1.ne'
    have ht1deg : t1.natDegree = n + 2 := by
      rw [ht1, natDegree_mul' hlcprod, natDegree_C_mul_X _ hd, hd1]; omega
    have ht1lc : t1.leadingCoeff = 2 * ((n : K) + 1 + a) * (gegenbauer a (n + 1)).leadingCoeff := by
      rw [ht1, leadingCoeff_mul' hlcprod, leadingCoeff_C_mul_X]
    have ht2deg : t2.natDegree ≤ n := (natDegree_C_mul_le _ _).trans hd0.le
    have hlt : t2.natDegree < t1.natDegree := by rw [ht1deg]; omega
    have hbdeg : (t1 - t2).natDegree = n + 2 :=
      (natDegree_sub_eq_left_of_natDegree_lt hlt).trans ht1deg
    have hlt2 : t2.natDegree < n + 2 := lt_of_le_of_lt ht2deg (by omega)
    have hblc : (t1 - t2).leadingCoeff = t1.leadingCoeff := by
      unfold leadingCoeff
      rw [hbdeg, ht1deg, coeff_sub, coeff_eq_zero_of_natDegree_lt hlt2, sub_zero]
    have hc : ((n : K) + 2)⁻¹ ≠ 0 := by positivity
    rw [gegenbauer_add_two]
    refine ⟨by rw [natDegree_C_mul hc, hbdeg], ?_⟩
    rw [leadingCoeff_mul' (by rw [hblc, ht1lc, leadingCoeff_C]; positivity),
      leadingCoeff_C, hblc, ht1lc]
    positivity

end Polynomial
