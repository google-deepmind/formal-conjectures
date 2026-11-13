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

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Derivative polynomials of the sigmoid

The integer polynomials $P_0(X)=X$ and $P_{n+1}(X)=X(1-X)P_n'(X)$ express the iterated
derivatives of `Real.sigmoid`. We also connect their values to the derivatives of
$c \mapsto e^c/(A+e^c)$ used in Appendix A.3 of Bajari, Fox, Kim, and Ryan,
*The Random Coefficients Logit Model Is Identified*
([September 2010 author manuscript](https://hdl.handle.net/1721.1/101264)).
-/

@[expose] public section

namespace Polynomial

/-- Integer polynomials expressing the successive derivatives of the sigmoid. -/
noncomputable def sigmoidDerivPoly : ℕ → ℤ[X]
  | 0 => X
  | n + 1 => X * (1 - X) * (sigmoidDerivPoly n).derivative

@[simp]
lemma sigmoidDerivPoly_zero : sigmoidDerivPoly 0 = X := rfl

lemma sigmoidDerivPoly_succ (n : ℕ) :
    sigmoidDerivPoly (n + 1) = X * (1 - X) * (sigmoidDerivPoly n).derivative := rfl

lemma sigmoidDerivPoly_one : sigmoidDerivPoly 1 = X * (1 - X) := by
  simp [sigmoidDerivPoly]

lemma sigmoidDerivPoly_two : sigmoidDerivPoly 2 = X * (1 - X) * (1 - 2 * X) := by
  rw [sigmoidDerivPoly_succ, sigmoidDerivPoly_one]
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_one]
  ring

lemma aeval_sigmoidDerivPoly_one_pos {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    0 < aeval x (sigmoidDerivPoly 1) := by
  simpa [sigmoidDerivPoly_one] using mul_pos hx.1 (sub_pos.mpr hx.2)

@[simp]
lemma aeval_zero_sigmoidDerivPoly_succ (n : ℕ) :
    aeval (0 : ℝ) (sigmoidDerivPoly (n + 1)) = 0 := by
  simp [sigmoidDerivPoly_succ]

@[simp]
lemma aeval_one_sigmoidDerivPoly_succ (n : ℕ) :
    aeval (1 : ℝ) (sigmoidDerivPoly (n + 1)) = 0 := by
  simp [sigmoidDerivPoly_succ]

lemma aeval_half_sigmoidDerivPoly_two :
    aeval (1 / 2 : ℝ) (sigmoidDerivPoly 2) = 0 := by
  norm_num [sigmoidDerivPoly_two, _root_.map_ofNat]

lemma aeval_half_sigmoidDerivPoly_four :
    aeval (1 / 2 : ℝ) (sigmoidDerivPoly 4) = 0 := by
  norm_num [sigmoidDerivPoly, derivative_mul, derivative_sub]

end Polynomial

namespace Real

/-- Each iterated derivative of the sigmoid is an integer polynomial in its value. -/
lemma iteratedDeriv_sigmoid (n : ℕ) (x : ℝ) :
    iteratedDeriv n sigmoid x = Polynomial.aeval (sigmoid x) (Polynomial.sigmoidDerivPoly n) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, funext ih]
    refine (((Polynomial.sigmoidDerivPoly n).hasDerivAt_aeval (sigmoid x)).comp x
      (hasDerivAt_sigmoid x)).deriv.trans ?_
    simp only [Polynomial.sigmoidDerivPoly_succ, map_mul, map_sub, map_one,
      Polynomial.aeval_X]
    ring

/-- The shifted sigmoid is the share function $e^c/(A+e^c)$. -/
lemma sigmoid_sub_log {A : ℝ} (hA : 0 < A) (c : ℝ) :
    sigmoid (c - log A) = exp c / (A + exp c) := by
  rw [sigmoid_def]
  have hexp : exp (-(c - log A)) = A / exp c := by
    rw [neg_sub, exp_sub, exp_log hA]
  rw [hexp]
  field_simp
  ring

/-- The derivative polynomials evaluate the mixed-logit share derivatives at the origin. -/
lemma iteratedDeriv_exp_div (n : ℕ) {A : ℝ} (hA : 0 < A) :
    iteratedDeriv n (fun c ↦ exp c / (A + exp c)) 0 =
      Polynomial.aeval (1 / (1 + A)) (Polynomial.sigmoidDerivPoly n) := by
  have hfun : (fun c ↦ exp c / (A + exp c)) = fun c ↦ sigmoid (c - log A) :=
    funext fun c ↦ (sigmoid_sub_log hA c).symm
  rw [hfun, iteratedDeriv_comp_sub_const]
  dsimp only
  rw [iteratedDeriv_sigmoid]
  congr 1
  rw [sigmoid_sub_log hA]
  simp [add_comm]

/-- If $A>1$, the share value at zero belongs to $(0,1/2)$. -/
lemma one_div_one_add_mem_Ioo {A : ℝ} (hA : 1 < A) :
    1 / (1 + A) ∈ Set.Ioo (0 : ℝ) (1 / 2) := by
  constructor
  · positivity
  · apply (div_lt_div_iff₀ (by positivity) (by norm_num)).2
    linarith

/-- Every value in $(0,1/2)$ is the share value at zero for some $A>1$. -/
lemma exists_one_div_one_add_eq {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
    ∃ A : ℝ, 1 < A ∧ 1 / (1 + A) = x := by
  refine ⟨x⁻¹ - 1, ?_, ?_⟩
  · have hinv := (inv_lt_inv₀ (by norm_num : (0 : ℝ) < 1 / 2) hx.1).2 hx.2
    norm_num at hinv
    linarith
  · have hcancel : 1 + (x⁻¹ - 1) = x⁻¹ := by ring
    rw [hcancel, one_div, inv_inv]

end Real
