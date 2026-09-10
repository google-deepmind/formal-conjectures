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

public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Quasi-isomorphisms between mapping cones

A commutative square of cochain complexes induces a map between its mapping cones. If both
vertical maps are quasi-isomorphisms, then so is the induced cone map. The proof applies the
five-lemma property for morphisms of distinguished triangles in the derived category.

This is the categorical comparison needed to pass from ordinary cohomology comparisons on a
space and an open complement to the corresponding comparison with support.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open CategoryTheory.Pretriangulated

universe u

namespace CochainComplex.mappingCone

set_option linter.style.haveILetI false in
/-- A map of mapping cones induced by a commutative square is a quasi-isomorphism when both
vertical maps in the square are quasi-isomorphisms. -/
lemma map_quasiIso_of_vertical_quasiIso
    {C : Type u} [Category C] [Abelian C] [HasDerivedCategory C]
    {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : φ₁ ≫ b = a ≫ φ₂) [QuasiIso a] [QuasiIso b] :
    QuasiIso (map φ₁ φ₂ a b comm) := by
  let tmap := (DerivedCategory.Q.mapTriangle).map
    (triangleMap φ₁ φ₂ a b comm)
  haveI : IsIso tmap.hom₁ := by
    change IsIso (DerivedCategory.Q.map a)
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  haveI : IsIso tmap.hom₂ := by
    change IsIso (DerivedCategory.Q.map b)
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  haveI : IsIso tmap.hom₃ :=
    CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂ tmap
      (DerivedCategory.mappingCone_triangle_distinguished φ₁)
      (DerivedCategory.mappingCone_triangle_distinguished φ₂)
      (inferInstance : IsIso tmap.hom₁) (inferInstance : IsIso tmap.hom₂)
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact (inferInstance : IsIso tmap.hom₃)

end CochainComplex.mappingCone
