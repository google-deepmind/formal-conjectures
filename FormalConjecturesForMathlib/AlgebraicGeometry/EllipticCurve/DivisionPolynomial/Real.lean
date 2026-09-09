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

public import FormalConjecturesForMathlib.Algebra.CubicDiscriminant
public import FormalConjecturesForMathlib.Analysis.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
public import Mathlib.Analysis.Polynomial.Order
public import Mathlib.Analysis.Real.Sqrt

@[expose] public noncomputable section

/-!
# The real roots of the 2-division polynomial

Let $W$ be a Weierstrass curve over $\mathbb{R}$, with equation
$y^2 + a_1 xy + a_3 y = x^3 + a_2 x^2 + a_4 x + a_6$. Completing the square,
$(2y + a_1 x + a_3)^2 = 4x^3 + b_2 x^2 + 2 b_4 x + b_6$, the *2-division polynomial*
`WeierstrassCurve.Ψ₂Sq`. Its real roots are the $x$-coordinates of the real points of order $2$,
and its sign cuts out the real locus: $W(\mathbb{R})$ consists of the point at infinity together
with the real points with $4x^3 + b_2 x^2 + 2 b_4 x + b_6 \geq 0$. This file describes its real
roots in terms of the sign of the discriminant $\Delta$, using that the discriminant of the cubic
is $16 \Delta$ (`WeierstrassCurve.twoTorsionPolynomial_discr`).

## Main definitions and statements

* `WeierstrassCurve.e₁`: the largest real root $e_1$ of the 2-division polynomial. The polynomial
  is positive to the right of $e_1$ (`WeierstrassCurve.eval_Ψ₂Sq_pos`) and, for an elliptic
  curve, $e_1$ is a simple root (`WeierstrassCurve.rootMultiplicity_e₁`), so that the polynomial
  factors as $(x - e_1) Q(x)$ with $Q$ positive on $[e_1, \infty)$
  (`WeierstrassCurve.exists_Ψ₂Sq_eq_X_sub_C_mul`).
* `WeierstrassCurve.eq_e₁_of_isRoot_of_neg`: if $\Delta < 0$ then $e_1$ is the only real root.
* `WeierstrassCurve.exists_three_roots_of_pos`: if $\Delta > 0$ then there are three real roots
  $e_3 < e_2 < e_1$, and $4x^3 + b_2 x^2 + 2 b_4 x + b_6 = 4 (x - e_1)(x - e_2)(x - e_3)$.
-/

open Filter Polynomial Set

namespace WeierstrassCurve

variable (W : WeierstrassCurve ℝ)

/- ## The largest real root -/

/-- The largest real root $e_1$ of the 2-division polynomial $4x^3 + b_2 x^2 + 2 b_4 x + b_6$. -/
def e₁ : ℝ := sSup {x : ℝ | W.Ψ₂Sq.IsRoot x}

lemma finite_setOf_isRoot_Ψ₂Sq : {x : ℝ | W.Ψ₂Sq.IsRoot x}.Finite :=
  finite_setOfPred_isRoot (W.Ψ₂Sq_ne_zero four_ne_zero)

lemma isRoot_e₁ : W.Ψ₂Sq.IsRoot W.e₁ :=
  Set.Nonempty.csSup_mem
    (exists_isRoot_of_odd_natDegree (by rw [W.natDegree_Ψ₂Sq four_ne_zero]; decide))
    W.finite_setOf_isRoot_Ψ₂Sq

lemma le_e₁_of_isRoot {x : ℝ} (hx : W.Ψ₂Sq.IsRoot x) : x ≤ W.e₁ :=
  le_csSup W.finite_setOf_isRoot_Ψ₂Sq.bddAbove hx

lemma e₁_eq_of_isRoot {e : ℝ} (he : W.Ψ₂Sq.IsRoot e) (h : ∀ x, e < x → ¬ W.Ψ₂Sq.IsRoot x) :
    W.e₁ = e :=
  le_antisymm (not_lt.mp fun hlt ↦ h _ hlt W.isRoot_e₁) (W.le_e₁_of_isRoot he)

lemma eval_Ψ₂Sq_pos {x : ℝ} (hx : W.e₁ < x) : 0 < W.Ψ₂Sq.eval x :=
  zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg (fun r hr ↦ (W.le_e₁_of_isRoot hr).trans_lt hx)
    (by rw [W.leadingCoeff_Ψ₂Sq four_ne_zero]; norm_num)

lemma eval_Ψ₂Sq_nonpos {x : ℝ} (hx : ∀ r, W.Ψ₂Sq.IsRoot r → x ≤ r) : W.Ψ₂Sq.eval x ≤ 0 := by
  simpa [W.natDegree_Ψ₂Sq four_ne_zero, pow_succ] using
    zero_le_negOnePow_mul_eval_of_le_roots_of_leadingCoeff_nonneg hx
      (by rw [W.leadingCoeff_Ψ₂Sq four_ne_zero]; norm_num)

lemma eventually_pow_three_le_eval_Ψ₂Sq : ∀ᶠ x in atTop, x ^ 3 ≤ W.Ψ₂Sq.eval x := by
  have h := W.Ψ₂Sq.isEquivalent_atTop_lead.isLittleO.def (by norm_num : (0 : ℝ) < 1 / 2)
  simp only [W.natDegree_Ψ₂Sq four_ne_zero, W.leadingCoeff_Ψ₂Sq four_ne_zero, Pi.sub_apply,
    Real.norm_eq_abs] at h
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * x ^ 3)] at hx
  linarith [(abs_le.mp hx).1, pow_nonneg hx0 3]

lemma rootMultiplicity_e₁ [W.IsElliptic] : rootMultiplicity W.e₁ W.Ψ₂Sq = 1 :=
  le_antisymm (Cubic.rootMultiplicity_le_one_of_discr_ne_zero (P := W.twoTorsionPolynomial)
      four_ne_zero (W.twoTorsionPolynomial_discr_ne_zero_of_isElliptic
        (isUnit_iff_ne_zero.mpr two_ne_zero)) _)
    ((rootMultiplicity_pos (W.Ψ₂Sq_ne_zero four_ne_zero)).mpr W.isRoot_e₁)

lemma exists_Ψ₂Sq_eq_X_sub_C_mul [W.IsElliptic] :
    ∃ Q : ℝ[X], W.Ψ₂Sq = (X - C W.e₁) * Q ∧ ∀ x, W.e₁ ≤ x → 0 < Q.eval x := by
  obtain ⟨Q, hQ, hdvd⟩ :=
    exists_eq_pow_rootMultiplicity_mul_and_not_dvd W.Ψ₂Sq (W.Ψ₂Sq_ne_zero four_ne_zero) W.e₁
  rw [W.rootMultiplicity_e₁, pow_one] at hQ
  refine ⟨Q, hQ, fun x hx ↦ zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg (fun r hr ↦ ?_) ?_⟩
  · exact ((W.le_e₁_of_isRoot (by rw [IsRoot, hQ, eval_mul, hr.eq_zero, mul_zero])).lt_of_ne
      fun h ↦ hdvd (dvd_iff_isRoot.mpr (h ▸ hr))).trans_le hx
  · rw [← leadingCoeff_monic_mul (monic_X_sub_C W.e₁), ← hQ, W.leadingCoeff_Ψ₂Sq four_ne_zero]
    norm_num

lemma eq_e₁_of_isRoot_of_neg (h : W.Δ < 0) {x : ℝ} (hx : W.Ψ₂Sq.IsRoot x) : x = W.e₁ := by
  have : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr h.ne⟩
  by_contra hne
  obtain ⟨Q, hQ, -⟩ := W.exists_Ψ₂Sq_eq_X_sub_C_mul
  obtain ⟨S, hS⟩ := dvd_iff_isRoot.mpr (show Q.IsRoot x by simpa [hQ, sub_eq_zero, hne] using hx)
  have : S.natDegree = 1 := by
    grind [natDegree_mul, natDegree_X_sub_C, mul_eq_zero, W.natDegree_Ψ₂Sq four_ne_zero]
  have : (W.Ψ₂Sq.map (RingHom.id ℝ)).Splits := by
    simpa [Polynomial.map_id, hQ, hS] using (Splits.X_sub_C _).mul ((Splits.X_sub_C _).mul
      (Splits.of_natDegree_le_one_of_invertible this.le
        (invertibleOfNonzero (leadingCoeff_ne_zero.mpr (by grind)))))
  linarith [W.twoTorsionPolynomial_discr,
    Cubic.discr_nonneg_of_splits (P := W.twoTorsionPolynomial) four_ne_zero this]

/- ## The three real roots when Δ > 0 -/

lemma Ψ₂Sq_eq_X_sub_C_e₁_mul : W.Ψ₂Sq = (X - C W.e₁) *
    (C 4 * X ^ 2 + C (W.b₂ + 4 * W.e₁) * X + C (2 * W.b₄ + W.b₂ * W.e₁ + 4 * W.e₁ ^ 2)) := by
  have h : 4 * W.e₁ ^ 3 + W.b₂ * W.e₁ ^ 2 + 2 * W.b₄ * W.e₁ + W.b₆ = 0 := by
    simpa [Ψ₂Sq] using W.isRoot_e₁
  refine Polynomial.funext fun x ↦ ?_
  simp only [Ψ₂Sq, eval_mul, eval_sub, eval_add, eval_X, eval_C, eval_pow]
  grind

lemma sixteen_mul_Δ_eq_sq_mul : 16 * W.Δ =
    (4 * W.e₁ ^ 2 + (W.b₂ + 4 * W.e₁) * W.e₁ + (2 * W.b₄ + W.b₂ * W.e₁ + 4 * W.e₁ ^ 2)) ^ 2 *
      ((W.b₂ + 4 * W.e₁) ^ 2 - 16 * (2 * W.b₄ + W.b₂ * W.e₁ + 4 * W.e₁ ^ 2)) := by
  have h : 4 * W.e₁ ^ 3 + W.b₂ * W.e₁ ^ 2 + 2 * W.b₄ * W.e₁ + W.b₆ = 0 := by
    simpa [Ψ₂Sq] using W.isRoot_e₁
  have : W.b₆ = -(4 * W.e₁ ^ 3 + W.b₂ * W.e₁ ^ 2 + 2 * W.b₄ * W.e₁) := by linarith
  rw [← W.twoTorsionPolynomial_discr, twoTorsionPolynomial, Cubic.discr, this]
  ring

lemma exists_three_roots_of_pos (h : 0 < W.Δ) : ∃ e₂ e₃ : ℝ, e₃ < e₂ ∧ e₂ < W.e₁ ∧
    W.Ψ₂Sq = C 4 * ((X - C W.e₁) * ((X - C e₂) * (X - C e₃))) := by
  have hid := W.sixteen_mul_Δ_eq_sq_mul
  set q₁ := W.b₂ + 4 * W.e₁ with hq₁
  set q₀ := 2 * W.b₄ + W.b₂ * W.e₁ + 4 * W.e₁ ^ 2 with hq₀
  set s := √(q₁ ^ 2 - 16 * q₀)
  have hdisc : 0 < q₁ ^ 2 - 16 * q₀ := by
    by_contra! hle
    grind [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (4 * W.e₁ ^ 2 + q₁ * W.e₁ + q₀)) hle]
  have hQ : C 4 * X ^ 2 + C q₁ * X + C q₀ =
      C 4 * ((X - C ((-q₁ + s) / 8)) * (X - C ((-q₁ - s) / 8))) := by
    refine Polynomial.funext fun x ↦ ?_
    simp only [eval_mul, eval_sub, eval_add, eval_X, eval_C, eval_pow]
    grind
  refine ⟨(-q₁ + s) / 8, (-q₁ - s) / 8, by linarith [Real.sqrt_pos.mpr hdisc], ?_, ?_⟩
  · have : 4 * W.e₁ ^ 2 + q₁ * W.e₁ + q₀ ≠ 0 := fun _ ↦ by grind
    exact (W.le_e₁_of_isRoot (by simp [IsRoot, W.Ψ₂Sq_eq_X_sub_C_e₁_mul]; grind)).lt_of_ne
      fun heq ↦ this (by grind [congrArg (eval W.e₁) hQ])
  · grind [W.Ψ₂Sq_eq_X_sub_C_e₁_mul]

variable {e₂ e₃ : ℝ}

lemma eval_Ψ₂Sq_of_factor (hF : W.Ψ₂Sq = C 4 * ((X - C W.e₁) * ((X - C e₂) * (X - C e₃))))
    (x : ℝ) : W.Ψ₂Sq.eval x = 4 * (x - W.e₁) * (x - e₂) * (x - e₃) := by
  grind [eval_mul, eval_sub, eval_X, eval_C]

end WeierstrassCurve
