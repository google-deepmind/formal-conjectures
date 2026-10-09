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

import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic

/-!
# Prime impulses and the discriminant -20 control

Positive coefficients of prime impulses do not imply a positive convolution
quadratic form. The two-point restriction already requires a diagonal at least
as large as the absolute off-diagonal entry. The actual von Mangoldt function
has value zero at 1 and a strictly positive value at 2.

The second calculation counts representations by the two reduced forms of
discriminant -20. The principal form fails multiplicativity at 2 times 3, while
the class sum passes this test. Consequently their formal logarithmic-derivative
coefficients at 6 differ. This is a finite arithmetic test, not a theorem about
zeros of either Epstein zeta function. For the analytic control see Yoonbok Lee,
"On the zeros of Epstein zeta functions", arXiv:1204.6297.
-/

set_option autoImplicit false

namespace AEGIS.RHEulerOperatorObstructionV1

/-- The real quadratic form of a symmetric two-point Toeplitz section. -/
def twoPointForm (d a x y : ℝ) : ℝ :=
  d * (x ^ 2 + y ^ 2) + 2 * a * x * y

/-- Exact criterion; positive entries alone do not suffice. -/
theorem twoPoint_nonnegative_iff (d a : ℝ) :
    (∀ x y : ℝ, 0 ≤ twoPointForm d a x y) ↔ |a| ≤ d := by
  constructor
  · intro h
    have hp := h 1 1
    have hm := h 1 (-1)
    dsimp [twoPointForm] at hp hm
    rw [abs_le]
    constructor <;> nlinarith
  · intro h x y
    have ha := abs_le.mp h
    have hp : 0 ≤ (d + a) / 2 := by linarith
    have hm : 0 ≤ (d - a) / 2 := by linarith
    have h1 := mul_nonneg hp (sq_nonneg (x + y))
    have h2 := mul_nonneg hm (sq_nonneg (x - y))
    dsimp [twoPointForm]
    nlinarith

/-- A positive-definite real kernel vanishing at the identity must vanish
everywhere. Only its necessary two-point positivity condition is used. -/
theorem zero_diagonal_positive_kernel_vanishes (K : ℝ → ℝ)
    (hpos : ∀ t x y : ℝ, 0 ≤ twoPointForm (K 0) (K t) x y)
    (hzero : K 0 = 0) : ∀ t : ℝ, K t = 0 := by
  intro t
  have h := (twoPoint_nonnegative_iff (K 0) (K t)).mp (hpos t)
  rw [hzero] at h
  exact abs_nonpos_iff.mp h

/-- Thus a nonzero correction supported outside a forbidden window cannot
itself be a positive-definite kernel. Signed corrections remain possible. -/
theorem no_nonzero_positive_forbidden_window_correction
    (K : ℝ → ℝ) (L : ℝ) (hL : 0 < L)
    (hsupport : ∀ t : ℝ, |t| < L → K t = 0)
    (hnonzero : ∃ t : ℝ, K t ≠ 0) :
    ¬ (∀ t x y : ℝ, 0 ≤ twoPointForm (K 0) (K t) x y) := by
  intro hpos
  have hzero : K 0 = 0 := hsupport 0 (by simpa using hL)
  obtain ⟨t, ht⟩ := hnonzero
  exact ht (zero_diagonal_positive_kernel_vanishes K hpos hzero t)

/-- The von Mangoldt-weighted section at the first prime is indefinite. -/
theorem vonMangoldt_twoPoint_indefinite :
    twoPointForm (ArithmeticFunction.vonMangoldt 1)
        (ArithmeticFunction.vonMangoldt 2) 1 (-1) < 0 ∧
      0 < twoPointForm (ArithmeticFunction.vonMangoldt 1)
        (ArithmeticFunction.vonMangoldt 2) 1 1 := by
  rw [ArithmeticFunction.vonMangoldt_apply_one,
    ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 2)]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  dsimp [twoPointForm]
  constructor <;> nlinarith

/-- A nonnegative von Mangoldt measure is not automatically a nonnegative
translation quadratic form, even on two points. -/
theorem vonMangoldt_weights_do_not_imply_operator_nonnegative :
    (∀ n : ℕ, 0 ≤ ArithmeticFunction.vonMangoldt n) ∧
      ¬ (∀ x y : ℝ,
        0 ≤ twoPointForm (ArithmeticFunction.vonMangoldt 1)
          (ArithmeticFunction.vonMangoldt 2) x y) := by
  refine ⟨fun _ => ArithmeticFunction.vonMangoldt_nonneg, ?_⟩
  intro h
  exact (not_lt_of_ge (h 1 (-1))) vonMangoldt_twoPoint_indefinite.1

/-- Principal reduced form of discriminant -20. -/
def principalForm (x y : ℤ) : ℤ := x ^ 2 + 5 * y ^ 2

/-- The other reduced form of discriminant -20. -/
def otherForm (x y : ℤ) : ℤ := 2 * x ^ 2 + 2 * x * y + 3 * y ^ 2

private theorem coord_bounds (x : ℤ) (n : ℕ) (h : x ^ 2 ≤ (n : ℤ)) :
    -(n : ℤ) ≤ x ∧ x ≤ (n : ℤ) := by
  have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  constructor
  · by_contra hb
    have hx : x ≤ -(n : ℤ) - 1 := by omega
    nlinarith [sq_nonneg (x + 1)]
  · by_contra hb
    have hx : (n : ℤ) + 1 ≤ x := by omega
    nlinarith [sq_nonneg (x - 1)]

/-- The finite enumeration used below includes every principal representation. -/
theorem principal_representation_bounds (x y : ℤ) (n : ℕ)
    (h : principalForm x y = (n : ℤ)) :
    (-(n : ℤ) ≤ x ∧ x ≤ (n : ℤ)) ∧
      (-(n : ℤ) ≤ y ∧ y ≤ (n : ℤ)) := by
  dsimp [principalForm] at h
  exact ⟨coord_bounds x n (by nlinarith [sq_nonneg y]),
    coord_bounds y n (by nlinarith [sq_nonneg x, sq_nonneg y])⟩

/-- The finite enumeration also includes every nonprincipal representation. -/
theorem other_representation_bounds (x y : ℤ) (n : ℕ)
    (h : otherForm x y = (n : ℤ)) :
    (-(n : ℤ) ≤ x ∧ x ≤ (n : ℤ)) ∧
      (-(n : ℤ) ≤ y ∧ y ≤ (n : ℤ)) := by
  dsimp [otherForm] at h
  exact ⟨coord_bounds x n (by nlinarith [sq_nonneg (x + y), sq_nonneg y]),
    coord_bounds y n (by nlinarith [sq_nonneg (x + y), sq_nonneg x, sq_nonneg y])⟩

/-- Representation counts divided by the two units, using the proved box. -/
noncomputable def coefficient (Q : ℤ → ℤ → ℤ) (n : ℕ) : ℕ :=
  ((Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter
    (fun p => Q p.1 p.2 = (n : ℤ))).card / 2

/-- Exact principal coefficients at the identity and the 2,3,6 control. -/
theorem principal_coefficients :
    coefficient principalForm 1 = 1 ∧ coefficient principalForm 2 = 0 ∧
      coefficient principalForm 3 = 0 ∧ coefficient principalForm 6 = 2 := by
  decide

/-- Exact coefficients for the other class in the same discriminant. -/
theorem other_coefficients :
    coefficient otherForm 1 = 0 ∧ coefficient otherForm 2 = 1 ∧
      coefficient otherForm 3 = 2 ∧ coefficient otherForm 6 = 0 := by
  decide

/-- The principal class violates multiplicativity at coprime arguments. -/
theorem principal_not_multiplicative_at_two_three :
    Nat.Coprime 2 3 ∧
      coefficient principalForm (2 * 3) ≠
        coefficient principalForm 2 * coefficient principalForm 3 := by
  norm_num [principal_coefficients.2.1, principal_coefficients.2.2.1,
    principal_coefficients.2.2.2]

/-- The class sum passes the same finite multiplicativity test. -/
theorem class_sum_multiplicative_at_two_three :
    coefficient principalForm 6 + coefficient otherForm 6 =
      (coefficient principalForm 2 + coefficient otherForm 2) *
        (coefficient principalForm 3 + coefficient otherForm 3) := by
  rw [principal_coefficients.2.1, principal_coefficients.2.2.1,
    principal_coefficients.2.2.2, other_coefficients.2.1,
    other_coefficients.2.2.1, other_coefficients.2.2.2]

/-- At the squarefree index 6 the Dirichlet convolution equation
`a * b = a log`, with `a(1)=1` and `b(1)=0`, determines `b(6)` as follows. -/
theorem logarithmic_derivative_at_six
    (a2 a3 a6 b2 b3 b6 : ℝ)
    (h2 : b2 = a2 * Real.log 2)
    (h3 : b3 = a3 * Real.log 3)
    (h6 : b6 + a2 * b3 + a3 * b2 = a6 * Real.log 6) :
    b6 = (a6 - a2 * a3) * Real.log 6 := by
  have hlog : Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
    calc
      Real.log (6 : ℝ) = Real.log ((2 : ℝ) * 3) := by norm_num
      _ = Real.log 2 + Real.log 3 :=
        Real.log_mul (by norm_num) (by norm_num)
  rw [h2, h3, hlog] at h6
  rw [hlog]
  nlinarith

/-- The principal coefficient defect at the non-prime-power index 6 is positive. -/
theorem principal_logarithmic_defect_positive :
    0 < (((coefficient principalForm 6 : ℕ) : ℝ) -
      (coefficient principalForm 2 : ℝ) *
      (coefficient principalForm 3 : ℝ)) * Real.log 6 := by
  rw [principal_coefficients.2.1, principal_coefficients.2.2.1,
    principal_coefficients.2.2.2]
  have hlog : 0 < Real.log 6 := Real.log_pos (by norm_num)
  positivity

end AEGIS.RHEulerOperatorObstructionV1

#print axioms AEGIS.RHEulerOperatorObstructionV1.twoPoint_nonnegative_iff
#print axioms AEGIS.RHEulerOperatorObstructionV1.no_nonzero_positive_forbidden_window_correction
#print axioms AEGIS.RHEulerOperatorObstructionV1.vonMangoldt_weights_do_not_imply_operator_nonnegative
#print axioms AEGIS.RHEulerOperatorObstructionV1.principal_representation_bounds
#print axioms AEGIS.RHEulerOperatorObstructionV1.other_representation_bounds
#print axioms AEGIS.RHEulerOperatorObstructionV1.principal_not_multiplicative_at_two_three
#print axioms AEGIS.RHEulerOperatorObstructionV1.class_sum_multiplicative_at_two_three
#print axioms AEGIS.RHEulerOperatorObstructionV1.logarithmic_derivative_at_six
#print axioms AEGIS.RHEulerOperatorObstructionV1.principal_logarithmic_defect_positive
