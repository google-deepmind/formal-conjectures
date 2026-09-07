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

import FormalConjecturesTest.RealPeriod.Eisenstein
import FormalConjecturesTest.RealPeriod.JSurjective
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Every short Weierstrass curve over ℂ comes from a lattice

For $A, B \in \mathbb{C}$ with $4A^3 + 27B^2 \neq 0$ there is a lattice with $g_2 = -4A$ and
$g_3 = -4B$ (`PeriodPair.exists_g₂_g₃`), so the curve $y^2 = x^3 + Ax + B$ is the curve
$y^2 = x^3 - \frac{g_2}{4} x - \frac{g_3}{4}$ of that lattice. Surjectivity of the modular
$j$-function gives $\tau$ with $j(\tau) = j(E)$, which forces
$B^2 g_2(\tau)^3 + 4 A^3 g_3(\tau)^2 = 0$, and a homothety of $\mathbb{Z} + \mathbb{Z}\tau$ then
matches the invariants exactly, since homothety by $\alpha$ scales $g_n$ by $\alpha^{-n}$.

Along the way the elliptic curve of a lattice is defined (`PeriodPair.weierstrassCurve`), with
its $j$-invariant $1728 g_2^3 / (g_2^3 - 27 g_3^2)$, which for $\mathbb{Z} + \mathbb{Z}\tau$ is
$j(\tau)$.

Ported from the LeanBridge development.
-/

open Complex UpperHalfPlane EisensteinSeries ModularForm
open scoped UpperHalfPlane CongruenceSubgroup MatrixGroups

noncomputable section

namespace WeierstrassCurve

/- ## Two facts about Weierstrass curves -/

lemma j_mul_Δ (W : WeierstrassCurve ℂ) [W.IsElliptic] : W.j * W.Δ = W.c₄ ^ 3 := by
  rw [WeierstrassCurve.j, ← WeierstrassCurve.coe_Δ']
  linear_combination W.c₄ ^ 3 * W.Δ'.inv_mul

/-- The short Weierstrass curve $y^2 = x^3 + A x + B$. -/
def short (A B : ℂ) : WeierstrassCurve ℂ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := A
  a₆ := B

lemma short_Δ (A B : ℂ) : (short A B).Δ = -16 * (4 * A ^ 3 + 27 * B ^ 2) := by
  simp only [short, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

lemma short_Δ_ne_zero {A B : ℂ} (h : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) : (short A B).Δ ≠ 0 := by
  rw [short_Δ]
  exact mul_ne_zero (by norm_num) h

lemma short_isElliptic {A B : ℂ} (h : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) : (short A B).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (short_Δ_ne_zero h)⟩

lemma short_c₄ (A B : ℂ) : (short A B).c₄ = -48 * A := by
  simp only [short, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

lemma short_j_mul_Δ (A B : ℂ) [(short A B).IsElliptic] :
    (short A B).j * (-16 * (4 * A ^ 3 + 27 * B ^ 2)) = (-48 * A) ^ 3 := by
  have := (short A B).j_mul_Δ
  rwa [short_Δ, short_c₄] at this

end WeierstrassCurve

namespace PeriodPair

/- ## The elliptic curve attached to a lattice -/

/-- The Weierstrass curve $y^2 = x^3 - \frac{g_2}{4} x - \frac{g_3}{4}$ attached to a period
lattice, the image of $\wp'^2 = 4 \wp^3 - g_2 \wp - g_3$ under
$(x, y) = (\wp, \frac{1}{2} \wp')$. -/
def weierstrassCurve (L : PeriodPair) : WeierstrassCurve ℂ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -L.g₂ / 4
  a₆ := -L.g₃ / 4

lemma weierstrassCurve_Δ (L : PeriodPair) :
    L.weierstrassCurve.Δ = weierstrassDiscriminant L := by
  grind [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, weierstrassCurve]

instance (L : PeriodPair) : L.weierstrassCurve.IsElliptic where
  isUnit := by
    simpa [weierstrassCurve_Δ] using isUnit_iff_ne_zero.mpr (weierstrassDiscriminant_ne_zero L)

lemma weierstrassCurve_c₄ (L : PeriodPair) : L.weierstrassCurve.c₄ = 12 * L.g₂ := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, weierstrassCurve]
  ring

/-- The $j$-invariant of the curve of a lattice is $1728 g_2^3 / (g_2^3 - 27 g_3^2)$. -/
theorem weierstrassCurve_j (L : PeriodPair) :
    L.weierstrassCurve.j = 1728 * L.g₂ ^ 3 / weierstrassDiscriminant L := by
  grind [WeierstrassCurve.j, Units.val_inv_eq_inv_val, ← div_eq_inv_mul, WeierstrassCurve.coe_Δ',
    weierstrassCurve_Δ, weierstrassCurve_c₄]

/-- The $j$-invariant of the curve of $\mathbb{Z} + \mathbb{Z}\tau$ is $j(\tau)$. -/
lemma weierstrassCurve_j_ofUpperHalfPlane (τ : ℍ) :
    (ofUpperHalfPlane τ).weierstrassCurve.j = ModularForm.j τ := by
  have : (riemannZeta 4 : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  have : (120 * riemannZeta 4 : ℂ) ≠ 0 := mul_ne_zero (by norm_num) this
  have : (120 * riemannZeta 4 : ℂ) ^ 3 ≠ 0 := pow_ne_zero _ this
  have : (E₄ τ : ℂ) ^ 3 - E₆ τ ^ 2 ≠ 0 := E₄_cube_sub_E₆_sq_ne_zero τ
  simp only [ModularForm.j, weierstrassCurve_j, weierstrassDiscriminant_ofUpperHalfPlane,
    g₂_ofUpperHalfPlane, mul_pow, CuspForm.coe_discriminant, discriminant_eq_E₄_cube_sub_E₆_sq]
  field_simp

/- ## Two elementary facts -/

lemma eq_zero_of_mul_pow_eq_zero (x : ℂ) {y : ℂ} (n : ℕ) (hn : n ≠ 0) (hx : x ≠ 0)
    (h : x * y ^ n = 0) : y = 0 :=
  (pow_eq_zero_iff hn).mp ((mul_eq_zero.mp h).resolve_left hx)

/-- In $\mathbb{C}$ the equation $\alpha^n d = c$ has a nonzero solution $\alpha$ whenever
$c, d \neq 0$ and $n \neq 0$. -/
lemma exists_pow_mul_eq (n : ℕ) (hn : n ≠ 0) (d : ℂ) {c : ℂ} (hc : c ≠ 0) (hd : d ≠ 0) :
    ∃ α : ℂ, α ≠ 0 ∧ α ^ n * d = c := by
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (c / d) (Nat.pos_of_ne_zero hn)
  refine ⟨α, fun h0 ↦ hc ?_, by rw [hα, div_mul_cancel₀ _ hd]⟩
  rw [h0, zero_pow hn] at hα
  exact (div_eq_zero_iff.mp hα.symm).resolve_right hd

lemma weierstrassCurve_j_mul_Δ (L : PeriodPair) :
    L.weierstrassCurve.j * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = (12 * L.g₂) ^ 3 := by
  have h := L.weierstrassCurve.j_mul_Δ
  rwa [weierstrassCurve_Δ, weierstrassDiscriminant, weierstrassCurve_c₄] at h

lemma g₃_ne_zero_of_g₂_eq_zero (L : PeriodPair) (h₂ : L.g₂ = 0) : L.g₃ ≠ 0 :=
  fun h₃ ↦ weierstrassDiscriminant_ne_zero L (by rw [weierstrassDiscriminant, h₂, h₃]; ring)

lemma g₂_ne_zero_of_g₃_eq_zero (L : PeriodPair) (h₃ : L.g₃ = 0) : L.g₂ ≠ 0 :=
  fun h₂ ↦ weierstrassDiscriminant_ne_zero L (by rw [weierstrassDiscriminant, h₂, h₃]; ring)

/- ## Homotheties of `ℤ + ℤτ` -/

lemma linearIndependent_scaled (τ : ℍ) {α : ℂ} (hα : α ≠ 0) :
    LinearIndependent ℝ ![α, α * (τ : ℂ)] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  rw [Complex.real_smul, Complex.real_smul] at hst
  have : (s : ℂ) + (t : ℂ) * (τ : ℂ) = 0 := by
    rcases mul_eq_zero.mp (show α * (s + t * τ) = 0 by grind) with h | h
    · exact absurd h hα
    · exact h
  refine (LinearIndependent.pair_iff.mp (linearIndependent_one_coe τ)) s t ?_
  rw [Complex.real_smul, Complex.real_smul]; grind

/-- The period pair $(\alpha, \alpha \tau)$, whose lattice is
$\alpha (\mathbb{Z} + \mathbb{Z}\tau)$. -/
def scaledPair (τ : ℍ) {α : ℂ} (hα : α ≠ 0) : PeriodPair where
  ω₁ := α
  ω₂ := α * (τ : ℂ)
  indep := linearIndependent_scaled τ hα

lemma scaledPair_ω₁ (τ : ℍ) {α : ℂ} (hα : α ≠ 0) : (scaledPair τ hα).ω₁ = α := rfl

lemma scaledPair_ω₂ (τ : ℍ) {α : ℂ} (hα : α ≠ 0) : (scaledPair τ hα).ω₂ = α * (τ : ℂ) := rfl

lemma scaledPair_τ (τ : ℍ) {α : ℂ} (hα : α ≠ 0) : (scaledPair τ hα).τ = τ := by
  have hdiv : (scaledPair τ hα).ω₂ / (scaledPair τ hα).ω₁ = (τ : ℂ) := by
    rw [scaledPair_ω₁, scaledPair_ω₂, mul_div_cancel_left₀ _ hα]
  refine UpperHalfPlane.ext ?_
  rw [coe_τ_of_im_pos _ (by rw [hdiv]; exact τ.im_pos), hdiv]

lemma G_scaledPair (τ : ℍ) {α : ℂ} (hα : α ≠ 0) (n : ℕ) :
    (scaledPair τ hα).G n = (α ^ n)⁻¹ * (ofUpperHalfPlane τ).G n := by
  have := G_eq_smul_of_latticeEquiv (scalingEquiv (scaledPair τ hα))
    (scalingEquiv_apply (scaledPair τ hα)) n
  rw [scaledPair_τ τ hα, scaledPair_ω₁, inv_pow, inv_inv] at this
  rw [this, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n hα), one_mul]

lemma g₂_scaledPair (τ : ℍ) {α : ℂ} (hα : α ≠ 0) :
    (scaledPair τ hα).g₂ = (α ^ 4)⁻¹ * (ofUpperHalfPlane τ).g₂ := by
  rw [PeriodPair.g₂, G_scaledPair τ hα 4, PeriodPair.g₂]; ring

lemma g₃_scaledPair (τ : ℍ) {α : ℂ} (hα : α ≠ 0) :
    (scaledPair τ hα).g₃ = (α ^ 6)⁻¹ * (ofUpperHalfPlane τ).g₃ := by
  rw [PeriodPair.g₃, G_scaledPair τ hα 6, PeriodPair.g₃]; ring

/-- A solution $\alpha$ of $\alpha^4 (-4A) = g_2(\tau)$ and $\alpha^6 (-4B) = g_3(\tau)$ gives
the lattice $\alpha (\mathbb{Z} + \mathbb{Z}\tau)$ with invariants $-4A$ and $-4B$. -/
lemma scaledPair_g₂_g₃ (τ : ℍ) {α : ℂ} (hα : α ≠ 0) {A B : ℂ}
    (h₂ : α ^ 4 * (-4 * A) = (ofUpperHalfPlane τ).g₂)
    (h₃ : α ^ 6 * (-4 * B) = (ofUpperHalfPlane τ).g₃) :
    (scaledPair τ hα).g₂ = -4 * A ∧ (scaledPair τ hα).g₃ = -4 * B :=
  ⟨by rw [g₂_scaledPair τ hα, ← h₂, inv_mul_cancel_left₀ (pow_ne_zero 4 hα)],
    by rw [g₃_scaledPair τ hα, ← h₃, inv_mul_cancel_left₀ (pow_ne_zero 6 hα)]⟩

/- ## Existence of the period lattice -/

/-- If $\mathbb{Z} + \mathbb{Z}\tau$ and the curve $y^2 = x^3 + Ax + B$ have the same
$j$-invariant then $B^2 g_2(\tau)^3 + 4 A^3 g_3(\tau)^2 = 0$. -/
lemma g₂_g₃_relation_of_j_eq {A B : ℂ} (τ : ℍ) [(WeierstrassCurve.short A B).IsElliptic]
    (hj : (ofUpperHalfPlane τ).weierstrassCurve.j = (WeierstrassCurve.short A B).j) :
    B ^ 2 * (ofUpperHalfPlane τ).g₂ ^ 3 + 4 * A ^ 3 * (ofUpperHalfPlane τ).g₃ ^ 2 = 0 := by
  have : (12 * (ofUpperHalfPlane τ).g₂) ^ 3 * (-16 * (4 * A ^ 3 + 27 * B ^ 2))
      = (-48 * A) ^ 3 * ((ofUpperHalfPlane τ).g₂ ^ 3 - 27 * (ofUpperHalfPlane τ).g₃ ^ 2) := by
    rw [← (ofUpperHalfPlane τ).weierstrassCurve_j_mul_Δ, ← WeierstrassCurve.short_j_mul_Δ A B, hj]
    ring
  linear_combination this / (-746496)

/-- **Existence of the period lattice.** For $4 A^3 + 27 B^2 \neq 0$ there is a lattice with
$g_2 = -4A$ and $g_3 = -4B$. Surjectivity of the modular $j$-function gives a $\tau$ with
$j(\tau) = j(E)$, and a homothety of $\mathbb{Z} + \mathbb{Z}\tau$ then matches the invariants,
since a homothety by $\alpha$ scales $g_n$ by $\alpha^{-n}$. -/
theorem exists_g₂_g₃ {A B : ℂ} (h : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) :
    ∃ L : PeriodPair, L.g₂ = -4 * A ∧ L.g₃ = -4 * B := by
  have := WeierstrassCurve.short_isElliptic h
  -- Choose `τ` with `j(ℤ + ℤτ) = j(y² = x³ + Ax + B)`.
  obtain ⟨τ, hτ⟩ := ModularForm.j_surjective (WeierstrassCurve.short A B).j
  have := g₂_g₃_relation_of_j_eq τ ((weierstrassCurve_j_ofUpperHalfPlane τ).trans hτ)
  rcases eq_or_ne A 0 with hA | hA
  · -- `A = 0`: then `g₂(τ) = 0`, and any `α` with `α⁶ · (-4B) = g₃(τ)` works.
    subst hA
    have hB : B ≠ 0 := by grind
    have hg₂0 : (ofUpperHalfPlane τ).g₂ = 0 := eq_zero_of_mul_pow_eq_zero (B ^ 2) 3 (by norm_num)
      (pow_ne_zero 2 hB) (by linear_combination this)
    obtain ⟨α, hα, hP6⟩ := exists_pow_mul_eq 6 (by norm_num) (-4 * B)
      ((ofUpperHalfPlane τ).g₃_ne_zero_of_g₂_eq_zero hg₂0) (mul_ne_zero (by norm_num) hB)
    exact ⟨scaledPair τ hα, scaledPair_g₂_g₃ τ hα (by rw [hg₂0]; ring) hP6⟩
  rcases eq_or_ne B 0 with hB | hB
  · -- `B = 0`: then `g₃(τ) = 0`, and any `α` with `α⁴ · (-4A) = g₂(τ)` works.
    subst hB
    have hg₃0 : (ofUpperHalfPlane τ).g₃ = 0 := eq_zero_of_mul_pow_eq_zero (4 * A ^ 3) 2
      (by norm_num) (mul_ne_zero (by norm_num) (pow_ne_zero 3 hA)) (by linear_combination this)
    obtain ⟨α, hα, hP4⟩ := exists_pow_mul_eq 4 (by norm_num) (-4 * A)
      ((ofUpperHalfPlane τ).g₂_ne_zero_of_g₃_eq_zero hg₃0) (mul_ne_zero (by norm_num) hA)
    exact ⟨scaledPair τ hα, scaledPair_g₂_g₃ τ hα hP4 (by rw [hg₃0]; ring)⟩
  · -- `A, B ≠ 0`: then `g₂(τ), g₃(τ) ≠ 0`, and any `α` with `α² = A g₃(τ) / (B g₂(τ))` works.
    have hg₂ne : (ofUpperHalfPlane τ).g₂ ≠ 0 := fun h₂ ↦
      (ofUpperHalfPlane τ).g₃_ne_zero_of_g₂_eq_zero h₂
      (eq_zero_of_mul_pow_eq_zero (4 * A ^ 3) 2 (by norm_num) (mul_ne_zero (by norm_num)
      (pow_ne_zero 3 hA)) (by linear_combination this - B ^ 2 * (ofUpperHalfPlane τ).g₂ ^ 2 * h₂))
    have hg₃ne : (ofUpperHalfPlane τ).g₃ ≠ 0 := fun h₃ ↦ hg₂ne
      (eq_zero_of_mul_pow_eq_zero (B ^ 2) 3 (by norm_num) (pow_ne_zero 2 hB)
      (by linear_combination this - 4 * A ^ 3 * (ofUpperHalfPlane τ).g₃ * h₃))
    set β := A * (ofUpperHalfPlane τ).g₃ / (B * (ofUpperHalfPlane τ).g₂) with hβ
    obtain ⟨α, hα2⟩ := IsAlgClosed.exists_pow_nat_eq β (n := 2) (by norm_num)
    have hα : α ≠ 0 := fun h0 ↦ (show β ≠ 0 by
      simpa [hβ] using div_ne_zero (mul_ne_zero hA hg₃ne) (mul_ne_zero hB hg₂ne)) (by grind)
    have hP4 : α ^ 4 * (-4 * A) = (ofUpperHalfPlane τ).g₂ := by
      have h4 : α ^ 4 = β ^ 2 := by grind
      rw [h4, hβ]
      field_simp
      linear_combination -this
    have hP6 : α ^ 6 * (-4 * B) = (ofUpperHalfPlane τ).g₃ := by
      have h6 : α ^ 6 = β ^ 3 := by
        rw [← hα2]
        ring
      rw [h6, hβ]
      field_simp
      linear_combination -this
    exact ⟨scaledPair τ hα, scaledPair_g₂_g₃ τ hα hP4 hP6⟩

end PeriodPair

end
