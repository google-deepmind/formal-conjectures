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
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.Analysis.Fourier.ZMod

@[expose] public section

namespace DirichletCharacter

open ZMod Finset

instance {S : Type*} [DecidableEq S] [CommRing S] {m : ℕ} :
    DecidablePred (Odd (S := S) (m := m)) :=
  fun ψ ↦ decidable_of_iff (ψ (-1) = -1) <| by rfl

instance {S : Type*} [DecidableEq S] [CommRing S] {m : ℕ} :
    DecidablePred (Even (S := S) (m := m)) :=
  fun ψ ↦ decidable_of_iff (ψ (-1) = 1) <| by rfl

section Comp

variable {R R' : Type*} [CommRing R] [CommRing R'] {N : ℕ} [NeZero N]
  {f : R →+* R'} {χ : DirichletCharacter R N}

/-- Post-composition with an injective ring homomorphism does not change the set of levels a
Dirichlet character factors through. -/
lemma factorsThrough_ringHomComp_iff (hf : Function.Injective f) {d : ℕ} :
    FactorsThrough (χ.ringHomComp f) d ↔ FactorsThrough χ d := by
  have hker : (χ.ringHomComp f).toUnitHom.ker = χ.toUnitHom.ker := by
    ext u
    simp only [MonoidHom.mem_ker, ← Units.val_inj, Units.val_one, MulChar.coe_toUnitHom,
      MulChar.ringHomComp_apply]
    exact ⟨fun h ↦ hf (by rw [h, map_one]), fun h ↦ by rw [h, map_one]⟩
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;>
    rw [factorsThrough_iff_ker_unitsMap h.dvd] <;>
    exact hker ▸ (factorsThrough_iff_ker_unitsMap h.dvd).mp h

/-- Post-composition with an injective ring homomorphism does not change the conductor. -/
lemma conductor_ringHomComp (hf : Function.Injective f) :
    conductor (χ.ringHomComp f) = conductor χ := by
  have h : conductorSet (χ.ringHomComp f) = conductorSet χ :=
    Set.ext fun _ ↦ factorsThrough_ringHomComp_iff hf
  simp [conductor, h]

/-- Post-composition with an injective ring homomorphism preserves primitivity. -/
lemma IsPrimitive.ringHomComp (hχ : χ.IsPrimitive) (hf : Function.Injective f) :
    IsPrimitive (χ.ringHomComp f) := by
  rwa [isPrimitive_def, conductor_ringHomComp hf]

end Comp

section Inv

variable {R : Type*} [CommMonoidWithZero R] {N : ℕ} {χ : DirichletCharacter R N}

/-- The inverse of a primitive Dirichlet character is primitive. -/
lemma IsPrimitive.inv (hχ : χ.IsPrimitive) : χ⁻¹.IsPrimitive := by
  rw [isPrimitive_def, conductor_inv]
  exact hχ

end Inv

section GaussSum

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- The Gauss sums of a primitive Dirichlet character and of its inverse multiply to
`χ (-1) * N`. Compare `gaussSum_mul_gaussSum_eq_card`, which assumes the source is a field. -/
theorem IsPrimitive.gaussSum_mul_gaussSum_inv (hχ : χ.IsPrimitive) :
    gaussSum χ stdAddChar * gaussSum χ⁻¹ stdAddChar = χ (-1) * N := by
  have h₁ : (𝓕 (⇑χ)) = fun k ↦ (fun j ↦ (⇑χ⁻¹) (-j)) k * gaussSum χ stdAddChar :=
    funext hχ.fourierTransform_eq_inv_mul_gaussSum
  have h₂ : (𝓕 (𝓕 (⇑χ))) 1 = χ 1 * gaussSum χ⁻¹ stdAddChar * gaussSum χ stdAddChar := by
    simp [h₁, ZMod.dft_mul_const, ZMod.dft_comp_neg, hχ.inv.fourierTransform_eq_inv_mul_gaussSum]
  simp only [ZMod.dft_dft, MulChar.map_one, one_mul, smul_eq_mul] at h₂
  linear_combination -h₂

/-- The Gauss sum of a primitive Dirichlet character does not vanish. -/
lemma IsPrimitive.gaussSum_ne_zero (hχ : χ.IsPrimitive) : gaussSum χ stdAddChar ≠ 0 := fun h ↦ by
  have h := h ▸ hχ.gaussSum_mul_gaussSum_inv
  rw [zero_mul] at h
  exact mul_ne_zero (MulChar.apply_ne_zero_iff.mpr isUnit_one.neg)
    (Nat.cast_ne_zero.mpr (NeZero.ne N)) h.symm

end GaussSum

section IsAlgebraic

variable {N : ℕ} [NeZero N]

/-- The values of a Dirichlet character over `ℂ` are algebraic. -/
lemma isAlgebraic_apply (χ : DirichletCharacter ℂ N) (a : ZMod N) : IsAlgebraic ℚ (χ a) := by
  rw [isAlgebraic_iff_isIntegral]
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    refine IsIntegral.of_pow (n := Fintype.card (ZMod N)ˣ) Fintype.card_pos ?_
    rw [← MulChar.pow_apply_coe, χ.pow_card_eq_one, MulChar.one_apply_coe]
    exact isIntegral_one
  · exact χ.map_nonunit ha ▸ isIntegral_zero

end IsAlgebraic

end DirichletCharacter
