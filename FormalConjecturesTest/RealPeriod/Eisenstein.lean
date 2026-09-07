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

import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing

/-!
# Lattice Eisenstein series as modular forms, and the discriminant of a lattice

For $\tau$ in the upper half plane the lattice Eisenstein series of $\mathbb{Z} + \mathbb{Z}\tau$
is a multiple of the modular Eisenstein series,
$G_k(\mathbb{Z} + \mathbb{Z}\tau) = 2 \zeta(k) E_k(\tau)$. Hence the discriminant
$g_2^3 - 27 g_3^2$ of $\mathbb{Z} + \mathbb{Z}\tau$ is a nonzero multiple of $E_4^3 - E_6^2$,
which never vanishes. Every lattice is a homothety of some $\mathbb{Z} + \mathbb{Z}\tau$, and the
discriminant scales by a nonzero factor under homothety, so the discriminant of every lattice is
nonzero: `PeriodPair.weierstrassDiscriminant_ne_zero`.

Ported from the LeanBridge development.
-/

open Complex UpperHalfPlane EisensteinSeries ModularForm
open scoped UpperHalfPlane CongruenceSubgroup MatrixGroups

noncomputable section

namespace PeriodPair

/- ## The period pair `(1, τ)` and its Eisenstein series -/

lemma linearIndependent_one_coe (τ : ℍ) : LinearIndependent ℝ ![1, (τ : ℂ)] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have : t * (τ : ℂ).im = 0 := by
    simpa [Complex.real_smul, Complex.add_im, Complex.mul_im] using congrArg Complex.im hst
  have : t = 0 := by
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h (by simpa [UpperHalfPlane.coe_im] using τ.im_ne_zero)
  refine ⟨?_, this⟩
  exact_mod_cast (show (s : ℂ) = 0 by simpa [this, Complex.real_smul] using hst)

/-- The period pair $(1, \tau)$ attached to $\tau$ in the upper half plane, whose lattice is
$\mathbb{Z} + \mathbb{Z}\tau$. -/
def ofUpperHalfPlane (τ : ℍ) : PeriodPair where
  ω₁ := 1
  ω₂ := τ
  indep := linearIndependent_one_coe τ

@[simp] lemma ofUpperHalfPlane_ω₁ (τ : ℍ) : (ofUpperHalfPlane τ).ω₁ = 1 := rfl

@[simp] lemma ofUpperHalfPlane_ω₂ (τ : ℍ) : (ofUpperHalfPlane τ).ω₂ = (τ : ℂ) := rfl

/-- The lattice sum $G_k(\mathbb{Z} + \mathbb{Z}\tau)$ reindexed as a sum over
$\mathbb{Z}^2$. -/
lemma G_eq_tsum_eisSummand (τ : ℍ) (k : ℕ) :
    (ofUpperHalfPlane τ).G k = ∑' v : Fin 2 → ℤ, eisSummand k v τ := by
  set L := ofUpperHalfPlane τ with hL
  set e := ((finTwoArrowEquiv ℤ).trans (Equiv.prodComm ℤ ℤ)).trans L.latticeEquivProd.symm.toEquiv
  rw [PeriodPair.G, ← e.tsum_eq]
  refine tsum_congr fun v => ?_
  have := L.latticeEquiv_symm_apply ((Equiv.prodComm ℤ ℤ) (finTwoArrowEquiv ℤ v))
  simp only [LinearEquiv.toEquiv_symm, Equiv.trans_apply, LinearEquiv.coe_symm_toEquiv, e] at ⊢ this
  rw [this, eisSummand, zpow_neg, zpow_natCast]
  simp [hL]; ring

theorem G_eq_riemannZeta_mul_eisensteinSeries (τ : ℍ) {k : ℕ} (hk : 3 ≤ k) :
    (ofUpperHalfPlane τ).G k = riemannZeta k * eisensteinSeries (N := 1) 0 k τ := by
  rw [G_eq_tsum_eisSummand, tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk]

lemma E_apply {k : ℕ} (hk : 3 ≤ k) (τ : ℍ) :
    (ModularForm.E hk τ : ℂ) = (1 / 2 : ℂ) * eisensteinSeries (N := 1) 0 k τ := rfl

/-- $G_k(\mathbb{Z} + \mathbb{Z}\tau) = 2 \zeta(k) E_k(\tau)$. -/
theorem G_eq_two_riemannZeta_mul_E (τ : ℍ) {k : ℕ} (hk : 3 ≤ k) :
    (ofUpperHalfPlane τ).G k = 2 * riemannZeta k * (ModularForm.E hk τ : ℂ) := by
  rw [G_eq_riemannZeta_mul_eisensteinSeries τ hk, E_apply]
  ring

/- ## Special values -/

open Real

theorem bernoulli'_five : bernoulli' 5 = 0 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose]

theorem bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, bernoulli'_five]

theorem riemannZeta_six : riemannZeta 6 = (π : ℂ) ^ 6 / 945 := by
  have h := riemannZeta_two_mul_nat (k := 3) (by norm_num)
  norm_num at h
  rw [h, bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_six]
  norm_num [Nat.factorial]
  ring

theorem zeta_const_identity : 27 * (280 * riemannZeta 6) ^ 2 = (120 * riemannZeta 4) ^ 3 := by
  rw [riemannZeta_four, riemannZeta_six]
  ring

/- ## The discriminant of `ℤ + ℤτ` -/

/-- The discriminant $g_2^3 - 27 g_3^2$ of the Weierstrass equation of a period lattice. The
discriminant of the cubic $4 x^3 - g_2 x - g_3$ is $16$ times this. -/
abbrev weierstrassDiscriminant (L : PeriodPair) : ℂ := L.g₂ ^ 3 - 27 * L.g₃ ^ 2

lemma g₂_ofUpperHalfPlane (τ : ℍ) :
    (ofUpperHalfPlane τ).g₂ = 120 * riemannZeta 4 * (E₄ τ : ℂ) := by
  rw [PeriodPair.g₂, G_eq_two_riemannZeta_mul_E τ (by norm_num)]
  push_cast
  ring

lemma g₃_ofUpperHalfPlane (τ : ℍ) :
    (ofUpperHalfPlane τ).g₃ = 280 * riemannZeta 6 * (E₆ τ : ℂ) := by
  rw [PeriodPair.g₃, G_eq_two_riemannZeta_mul_E τ (by norm_num)]
  push_cast
  ring

lemma weierstrassDiscriminant_ofUpperHalfPlane (τ : ℍ) :
    weierstrassDiscriminant (ofUpperHalfPlane τ)
      = (120 * riemannZeta 4) ^ 3 * (E₄ τ ^ 3 - E₆ τ ^ 2) := by
  rw [weierstrassDiscriminant, g₂_ofUpperHalfPlane, g₃_ofUpperHalfPlane]
  linear_combination (-(E₆ τ ^ 2)) * zeta_const_identity

lemma E₄_cube_sub_E₆_sq_ne_zero (τ : ℍ) : E₄ τ ^ 3 - E₆ τ ^ 2 ≠ 0 :=
  fun h ↦ discriminant_ne_zero τ (by grind [discriminant_eq_E₄_cube_sub_E₆_sq])

theorem weierstrassDiscriminant_ofUpperHalfPlane_ne_zero (τ : ℍ) :
    weierstrassDiscriminant (ofUpperHalfPlane τ) ≠ 0 := by
  rw [weierstrassDiscriminant_ofUpperHalfPlane]
  refine mul_ne_zero (pow_ne_zero _ (mul_ne_zero (by norm_num) ?_)) (E₄_cube_sub_E₆_sq_ne_zero τ)
  exact riemannZeta_ne_zero_of_one_lt_re (by norm_num)

/- ## Every lattice is a homothety of some `ℤ + ℤτ` -/

lemma ω₁_ne_zero (L : PeriodPair) : L.ω₁ ≠ 0 := by
  simpa using L.indep.ne_zero 0

/-- The period ratio $\omega_2 / \omega_1$ is not real. -/
lemma im_ω₂_div_ω₁_ne_zero (L : PeriodPair) : (L.ω₂ / L.ω₁).im ≠ 0 := by
  intro h
  have hre : (L.ω₂ / L.ω₁ : ℂ) = ((L.ω₂ / L.ω₁).re : ℝ) := by
    apply Complex.ext <;> simp [h]
  have hω₂ : (L.ω₂ / L.ω₁).re • L.ω₁ = L.ω₂ := by
    have hω₁ := L.ω₁_ne_zero
    rw [Complex.real_smul, ← hre]
    field_simp
  have h0 : (L.ω₂ / L.ω₁).re • L.ω₁ + (-1 : ℝ) • L.ω₂ = 0 := by rw [hω₂]; simp
  exact absurd ((LinearIndependent.pair_iff.mp L.indep) _ _ h0).2 (by norm_num)

/-- The normalised period ratio $\tau = \pm \omega_2 / \omega_1$, with the sign making it lie
in the upper half plane. -/
def τ (L : PeriodPair) : ℍ :=
  if h : 0 < (L.ω₂ / L.ω₁).im then UpperHalfPlane.mk (L.ω₂ / L.ω₁) h
  else UpperHalfPlane.mk (-(L.ω₂ / L.ω₁)) (by
    rw [Complex.neg_im, neg_pos]
    exact lt_of_le_of_ne (not_lt.mp h) L.im_ω₂_div_ω₁_ne_zero)

lemma coe_τ_of_im_pos (L : PeriodPair) (h : 0 < (L.ω₂ / L.ω₁).im) :
    (L.τ : ℂ) = L.ω₂ / L.ω₁ := by
  unfold PeriodPair.τ
  rw [dif_pos h]

lemma coe_τ_of_im_nonpos (L : PeriodPair) (h : ¬ 0 < (L.ω₂ / L.ω₁).im) :
    (L.τ : ℂ) = -(L.ω₂ / L.ω₁) := by
  unfold PeriodPair.τ
  rw [dif_neg h]

/-- The homothety by $\omega_1^{-1}$, carrying $\Lambda$ onto $\mathbb{Z} + \mathbb{Z}\tau$, as
a bijection of lattices. -/
def scalingEquiv (L : PeriodPair) : L.lattice ≃ (ofUpperHalfPlane L.τ).lattice :=
  L.latticeEquivProd.toEquiv.trans ((if 0 < (L.ω₂ / L.ω₁).im then Equiv.refl (ℤ × ℤ) else
    Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)).trans
    (ofUpperHalfPlane L.τ).latticeEquivProd.symm.toEquiv)

lemma scalingEquiv_apply (L : PeriodPair) (x : L.lattice) : scalingEquiv L x = (L.ω₁)⁻¹ * x := by
  have := by simpa [L.latticeEquivProd.symm_apply_apply] using
    L.latticeEquiv_symm_apply (L.latticeEquivProd x)
  set σ : ℤ × ℤ ≃ ℤ × ℤ := if 0 < (L.ω₂ / L.ω₁).im then Equiv.refl (ℤ × ℤ)
    else Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ) with hσ
  have h : (scalingEquiv L x : ℂ) = (σ (L.latticeEquivProd x)).1 * (ofUpperHalfPlane L.τ).ω₁
      + (σ (L.latticeEquivProd x)).2 * (ofUpperHalfPlane L.τ).ω₂ :=
    (ofUpperHalfPlane L.τ).latticeEquiv_symm_apply (σ (L.latticeEquivProd x))
  rw [h, this, ofUpperHalfPlane_ω₁, ofUpperHalfPlane_ω₂]
  by_cases h : 0 < (L.ω₂ / L.ω₁).im
  · rw [L.coe_τ_of_im_pos h, hσ, if_pos h, Equiv.refl_apply]
    field_simp [L.ω₁_ne_zero]
  · rw [L.coe_τ_of_im_nonpos h, hσ, if_neg h, Equiv.prodCongr_apply, Equiv.coe_refl,
      Equiv.neg_apply, Prod.map_fst, Prod.map_snd, id_eq]
    push_cast
    field_simp [L.ω₁_ne_zero]

/-- A bijection of lattices that scales by $c$ scales $G_n$ by $c^{-n}$. -/
lemma G_eq_smul_of_latticeEquiv {L L' : PeriodPair} {c : ℂ} (e : L.lattice ≃ L'.lattice)
    (he : ∀ x : L.lattice, e x = c * x) (n : ℕ) : L'.G n = (c ^ n)⁻¹ * L.G n := by
  simpa [PeriodPair.G, ← e.tsum_eq, ← tsum_mul_left] using tsum_congr fun x ↦
    by rw [he, mul_pow, mul_inv]

lemma weierstrassDiscriminant_smul_eq {L L' : PeriodPair} {c : ℂ} (hc : c ≠ 0)
    (e : L.lattice ≃ L'.lattice) (he : ∀ x, e x = c * x) :
    weierstrassDiscriminant L' = (c ^ 12)⁻¹ * weierstrassDiscriminant L := by
  simp only [weierstrassDiscriminant, PeriodPair.g₂, PeriodPair.g₃, G_eq_smul_of_latticeEquiv e he]
  field_simp

/-- The discriminant of a period lattice never vanishes. -/
theorem weierstrassDiscriminant_ne_zero (L : PeriodPair) : weierstrassDiscriminant L ≠ 0 := by
  refine fun _ ↦ weierstrassDiscriminant_ofUpperHalfPlane_ne_zero L.τ ?_
  rw [weierstrassDiscriminant_smul_eq (inv_ne_zero L.ω₁_ne_zero) _ (scalingEquiv_apply L)]
  grind

end PeriodPair

end
