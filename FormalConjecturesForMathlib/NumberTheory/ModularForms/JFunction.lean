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

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.Algebraic.Defs

/-!
# The modular $j$-function, CM points and rational Möbius transformations

This file collects the basic vocabulary shared by conjectures about the arithmetic of the modular
$j$-function, such as the modular Schanuel conjecture and the modular Zilber–Pink conjecture.

## Main definitions

- `ModularForm.j`: the modular $j$-function $j = E_4^3 / \Delta$ on the upper half-plane.
- `UpperHalfPlane.IsCMPoint`: points of the upper half-plane satisfying a non-trivial quadratic
  equation with integer coefficients; their $j$-values are the *singular moduli*.
- `UpperHalfPlane.moebius`: the Möbius action of $\mathrm{GL}_2^+(\mathbb{Q})$ on the upper
  half-plane.
- `UpperHalfPlane.IsGLPosRatEquiv`: the relation of lying in the same
  $\mathrm{GL}_2^+(\mathbb{Q})$-orbit. Two points are related if and only if their $j$-values are
  linked by a modular polynomial.

## Main results

- `ModularForm.j_smul`, `ModularForm.j_SL_smul`: the $j$-function is invariant under
  $\mathrm{SL}_2(\mathbb{Z})$.
- `UpperHalfPlane.isCMPoint_I`, `UpperHalfPlane.IsCMPoint.isAlgebraic`: $i$ is a CM point, and
  every CM point is algebraic over $\mathbb{Q}$.
- `UpperHalfPlane.moebius_one`, `UpperHalfPlane.moebius_mul`,
  `UpperHalfPlane.IsGLPosRatEquiv.equivalence`: `moebius` is a group action, so
  `IsGLPosRatEquiv` is an equivalence relation.
-/

@[expose] public section

open UpperHalfPlane SlashInvariantForm Polynomial
open scoped MatrixGroups

namespace ModularForm

/-- The modular $j$-function $j = E_4^3 / \Delta$, where $E_4$ is the normalised Eisenstein series
of weight $4$ and $\Delta$ is the modular discriminant. With these normalisations
$j(z) = q^{-1} + 744 + 196884 q + \dots$ where $q = e^{2\pi i z}$. -/
noncomputable def j (z : ℍ) : ℂ := E₄ z ^ 3 / discriminant z

/-- The $j$-function is invariant under the image `𝒮ℒ` of $\mathrm{SL}_2(\mathbb{Z})$ in
$\mathrm{GL}_2(\mathbb{R})$: $E_4^3$ and $\Delta$ are both modular of weight $12$, so their
automorphy factors cancel. -/
lemma j_smul {γ : GL (Fin 2) ℝ} (hγ : γ ∈ 𝒮ℒ) (z : ℍ) : j (γ • z) = j z := by
  have h4 : E₄ (γ • z) = denom γ z ^ 4 * E₄ z := by
    simpa using slash_action_eqn'' E₄ hγ z
  have h12 : discriminant (γ • z) = denom γ z ^ 12 * discriminant z := by
    simpa using slash_action_eqn'' CuspForm.discriminant hγ z
  simp [j, h4, h12, mul_pow, ← pow_mul, mul_div_mul_left, denom_ne_zero]

/-- The $j$-function is invariant under $\mathrm{SL}_2(\mathbb{Z})$. -/
lemma j_SL_smul (γ : SL(2, ℤ)) (z : ℍ) : j (γ • z) = j z :=
  j_smul ⟨γ, rfl⟩ z

end ModularForm

namespace UpperHalfPlane

/-- A point $z$ of the upper half-plane is a *CM point* (also called a *special point*) if it
satisfies a non-trivial quadratic equation with integer coefficients. Its image $j(z)$ under the
modular $j$-function is a *singular modulus*. -/
def IsCMPoint (z : ℍ) : Prop := ∃ a b c : ℤ, a ≠ 0 ∧ a * (z : ℂ) ^ 2 + b * z + c = 0

/-- The point $i$ is a CM point, since $i^2 + 1 = 0$. -/
lemma isCMPoint_I : IsCMPoint I :=
  ⟨1, 0, 1, one_ne_zero, by simp [coe_I, Complex.I_sq]⟩

/-- A CM point is an algebraic number, as a root of a nonzero integer quadratic. -/
lemma IsCMPoint.isAlgebraic {z : ℍ} (hz : IsCMPoint z) : IsAlgebraic ℚ (z : ℂ) := by
  obtain ⟨a, b, c, ha, h⟩ := hz
  exact ⟨C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ),
    fun h0 ↦ ha (by simpa [-map_intCast] using congrArg (coeff · 2) h0), by simp [h]⟩

/-- The Möbius action of $\mathrm{GL}_2^+(\mathbb{Q})$ on the upper half-plane, obtained by viewing
a rational matrix with positive determinant as a real one. -/
noncomputable def moebius (g : GL(2, ℚ)⁺) (z : ℍ) : ℍ :=
  Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (g : GL (Fin 2) ℚ) • z

/-- The identity matrix acts trivially. -/
@[simp]
lemma moebius_one (z : ℍ) : moebius 1 z = z := by
  simp [moebius]

/-- `moebius` is compatible with multiplication, so it is a group action. -/
lemma moebius_mul (g h : GL(2, ℚ)⁺) (z : ℍ) : moebius (g * h) z = moebius g (moebius h z) := by
  simp [moebius, mul_smul]

/-- Two points of the upper half-plane are $\mathrm{GL}_2^+(\mathbb{Q})$-equivalent if one is the
image of the other under a Möbius transformation with rational coefficients and positive
determinant. -/
def IsGLPosRatEquiv (z w : ℍ) : Prop := ∃ g : GL(2, ℚ)⁺, moebius g z = w

/-- Every point is equivalent to itself. -/
lemma IsGLPosRatEquiv.refl (z : ℍ) : IsGLPosRatEquiv z z := ⟨1, moebius_one z⟩

/-- The relation is symmetric: apply the inverse matrix. -/
lemma IsGLPosRatEquiv.symm {z w : ℍ} (h : IsGLPosRatEquiv z w) : IsGLPosRatEquiv w z := by
  obtain ⟨g, rfl⟩ := h
  exact ⟨g⁻¹, by simp [← moebius_mul]⟩

/-- The relation is transitive: compose the matrices. -/
lemma IsGLPosRatEquiv.trans {z w v : ℍ} (h₁ : IsGLPosRatEquiv z w) (h₂ : IsGLPosRatEquiv w v) :
    IsGLPosRatEquiv z v := by
  obtain ⟨g, rfl⟩ := h₁
  obtain ⟨h, rfl⟩ := h₂
  exact ⟨h * g, moebius_mul h g z⟩

/-- Lying in the same $\mathrm{GL}_2^+(\mathbb{Q})$-orbit is an equivalence relation. -/
lemma IsGLPosRatEquiv.equivalence : Equivalence IsGLPosRatEquiv :=
  ⟨IsGLPosRatEquiv.refl, IsGLPosRatEquiv.symm, IsGLPosRatEquiv.trans⟩

end UpperHalfPlane
