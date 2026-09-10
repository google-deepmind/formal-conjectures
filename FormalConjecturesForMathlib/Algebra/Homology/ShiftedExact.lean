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

public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Shift.ShiftedHom
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

import Mathlib.CategoryTheory.Triangulated.Yoneda

/-!
# Exactness for shifted morphisms

This file gives the elementwise exactness statement for morphisms into a distinguished triangle
in an arbitrary shifted degree. It is the shifted version of
`Pretriangulated.Triangle.coyoneda_exact₁`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u

namespace CategoryTheory.ShiftedHom

variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
  {X Y Z : C}

/-- Postcomposition with an invertible shifted morphism is a bijection on every shifted Hom.
The shift-addition associator is included explicitly, so the source and target degrees may be
written in any provably equal normal form. -/
noncomputable def postcompEquivOfIsIso {a b c : ℤ}
    (g : ShiftedHom Y Z b) [IsIso g] (h : b + a = c) :
    ShiftedHom X Y a ≃ ShiftedHom X Z c :=
  (Iso.refl X).homCongr
    (asIso (g⟦a⟧') ≪≫ (shiftFunctorAdd' C b a c h).symm.app Z)

@[simp] lemma postcompEquivOfIsIso_apply {a b c : ℤ}
    (g : ShiftedHom Y Z b) [IsIso g] (h : b + a = c)
    (f : ShiftedHom X Y a) :
    postcompEquivOfIsIso g h f = f.comp g h := by
  simp [postcompEquivOfIsIso, ShiftedHom.comp]

end CategoryTheory.ShiftedHom

namespace CategoryTheory.Pretriangulated.Triangle

variable {C : Type u} [Category.{v} C] [Limits.HasZeroObject C]
  [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Exactness at the first object of a distinguished triangle, in an arbitrary shifted degree. -/
lemma shifted_coyoneda_exact₁ (T : Triangle C) (hT : T ∈ distTriang C)
    (I : C) (n : ℤ) (α : ShiftedHom I T.obj₁ n)
    (hα : α.comp (ShiftedHom.mk₀ (0 : ℤ) rfl T.mor₁)
      (show (0 : ℤ) + n = n by lia) = 0) :
    ∃ β : ShiftedHom I T.obj₃ (n - 1),
      β.comp T.mor₃ (show (1 : ℤ) + (n - 1) = n by lia) = α := by
  let F := preadditiveCoyoneda.obj (Opposite.op I)
  have hexact := F.homologySequence_exact₁ T hT (n - 1) n (by lia)
  rw [ShortComplex.ab_exact_iff] at hexact
  have hkernel : ((F.shift n).map T.mor₁) α = 0 := by
    change α ≫ T.mor₁⟦n⟧' = 0
    simpa only [ShiftedHom.comp_mk₀] using hα
  obtain ⟨β, hβ⟩ := hexact α hkernel
  refine ⟨β, ?_⟩
  change F.homologySequenceδ T (n - 1) n (by lia) β = α at hβ
  rwa [preadditiveCoyoneda_homologySequenceδ_apply] at hβ

end CategoryTheory.Pretriangulated.Triangle
