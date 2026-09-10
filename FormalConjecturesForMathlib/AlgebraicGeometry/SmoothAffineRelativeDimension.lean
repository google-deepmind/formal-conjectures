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

public import FormalConjecturesForMathlib.AlgebraicGeometry.SmoothEquidimensional

/-!
# Actual equidimensional smooth affine neighborhoods

A proved standard-smooth affine presentation induces a genuine scheme morphism smooth
of that same relative dimension. This small adapter turns the local dimension bounds of
the canonical singular stratification into inputs for the constructed normal-coordinate
theorems, without assuming global equidimensionality of a stratum.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

open _root_.RingHom

universe u

/-- The restriction to actual affine source and target charts is smooth of the relative
dimension proved by its standard-smooth ring presentation. -/
theorem smoothOfRelativeDimension_resLE_of_isStandardSmooth
    {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U) {n : ℕ}
    (hstd : (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension n) :
    SmoothOfRelativeDimension n (f.resLE U V e) := by
  let : IsAffine U := hU
  let : IsAffine V := hV
  rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension n)]
  let : (toMorphismProperty (Locally (IsStandardSmoothOfRelativeDimension n))).RespectsIso :=
    toMorphismProperty_respectsIso_iff.mp
      (locally_respectsIso isStandardSmoothOfRelativeDimension_respectsIso)
  exact (MorphismProperty.arrow_mk_iso_iff
    (toMorphismProperty (Locally (IsStandardSmoothOfRelativeDimension n)))
      (arrowResLEAppIso f U V e)).mpr
        (locally_of isStandardSmoothOfRelativeDimension_respectsIso _ hstd)

set_option backward.isDefEq.respectTransparency false in
/-- A standard-smooth affine open of a complex scheme is an actual smooth complex
scheme of that precise relative dimension. -/
theorem smoothOfRelativeDimension_affineOpen_of_isStandardSmooth
    {X : Scheme} (f : X ⟶ Spec (.of ℂ)) {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ}
    (hstd : (f.appLE ⊤ U (by simp)).hom.IsStandardSmoothOfRelativeDimension n) :
    SmoothOfRelativeDimension n (U.ι ≫ f) := by
  let g := f.resLE ⊤ U (by simp)
  let : SmoothOfRelativeDimension n g :=
    smoothOfRelativeDimension_resLE_of_isStandardSmooth f (isAffineOpen_top _) hU _ hstd
  have h := smoothOfRelativeDimension_comp n 0 g (⊤ : (Spec (.of ℂ)).Opens).ι
  simpa only [Nat.add_zero, g, Scheme.Hom.resLE_comp_ι] using h

end AlgebraicGeometry
