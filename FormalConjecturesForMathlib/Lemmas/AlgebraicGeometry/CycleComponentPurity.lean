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

public import FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.CycleComponentPurity

import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.CycleComponentClosedPointDimension
import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.ProjectiveAnalytificationHausdorff
import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.ChartLocalFundamentalClassGenerator
import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.LocalFundamentalClassGenerator
import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.PuncturedEuclideanFundamentalClass

/-!
# Local dual classes on cycle components

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.CycleComponentPurity`.
-/

@[expose] public noncomputable section

open CategoryTheory Topology

namespace AlgebraicTopology.Singular

variable {R M : Type*} [Field R] [AddCommGroup M] [Module R M]

/-- A normalized dual is unique when its distinguished vector generates the module. -/
lemma normalizedDual_unique {z : M} (hz : z ≠ 0)
    (hzspan : Submodule.span R {z} = ⊤)
    (φ : Module.Dual R M) (hφ : φ z = 1) :
    φ = normalizedDual z hz := by
  ext y
  obtain ⟨a, rfl⟩ := (Submodule.span_singleton_eq_top_iff R z).mp hzspan y
  simp [hφ]

/-- The normalized dual of a homology generator generates the full dual space. -/
lemma span_normalizedDual_eq_top {z : M} (hz : z ≠ 0)
    (hzspan : Submodule.span R {z} = ⊤) :
    Submodule.span R {normalizedDual (R := R) z hz} = ⊤ := by
  rw [Submodule.span_singleton_eq_top_iff R]
  intro φ
  refine ⟨φ z, ?_⟩
  ext y
  obtain ⟨a, rfl⟩ := (Submodule.span_singleton_eq_top_iff R z).mp hzspan y
  simp

@[simp]
lemma linearEquivOfNormalizedGenerators_apply
    {N : Type*} [AddCommGroup N] [Module R N]
    (x : M) (hx : x ≠ 0) (hxspan : Submodule.span R {x} = ⊤)
    (y : N) (hy : y ≠ 0) (hyspan : Submodule.span R {y} = ⊤)
    (z : M) :
    linearEquivOfNormalizedGenerators x hx hxspan y hy hyspan z =
      (normalizedDual (R := R) x hx z : R) • y :=
  rfl

@[simp]
lemma linearEquivOfNormalizedGenerators_apply_generator
    {N : Type*} [AddCommGroup N] [Module R N]
    (x : M) (hx : x ≠ 0) (hxspan : Submodule.span R {x} = ⊤)
    (y : N) (hy : y ≠ 0) (hyspan : Submodule.span R {y} = ⊤) :
    linearEquivOfNormalizedGenerators x hx hxspan y hy hyspan x = y := by
  change (normalizedDual (R := R) x hx x : R) • y = y
  rw [normalizedDual_apply_self, one_smul]

/-- Sending the distinguished generator to the distinguished generator uniquely characterizes
the normalized equivalence. -/
lemma linearEquivOfNormalizedGenerators_unique
    {N : Type*} [AddCommGroup N] [Module R N]
    (x : M) (hx : x ≠ 0) (hxspan : Submodule.span R {x} = ⊤)
    (y : N) (hy : y ≠ 0) (hyspan : Submodule.span R {y} = ⊤)
    (e : M ≃ₗ[R] N) (he : e x = y) :
    e = linearEquivOfNormalizedGenerators x hx hxspan y hy hyspan := by
  ext z
  obtain ⟨a, rfl⟩ := (Submodule.span_singleton_eq_top_iff R x).mp hxspan z
  simp [he]

end AlgebraicTopology.Singular

namespace AlgebraicGeometry.CycleComponentSeparateLocalCoordinates

open AlgebraicTopology.Singular

noncomputable local instance {Y : Over (Spec ↧ℂ)} :
    TopologicalSpace (ComplexPoint Y) := Point.analyticTopology

variable {d n : ℕ} {X : Over (Spec ↧ℂ)} [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom] {x : X.left}
  [SmoothOfRelativeDimension d X.hom]
  (C : CycleComponentSeparateLocalCoordinates X x d n)

@[simp]
lemma neighborhoodLocalCoclass_apply_localClass :
    C.neighborhoodLocalCoclass C.neighborhoodLocalClass = 1 :=
  normalizedDual_apply_self C.neighborhoodLocalClass
    C.neighborhoodLocalClass_ne_zero

/-- The normalized local coclass generates cohomology supported at the selected smooth point of
the component neighborhood. -/
lemma span_neighborhoodLocalCoclass_eq_top :
    Submodule.span ℚ {C.neighborhoodLocalCoclass} = ⊤ :=
  span_normalizedDual_eq_top C.neighborhoodLocalClass_ne_zero
    C.span_neighborhoodLocalClass_eq_top

/-- The local normalization condition characterizes the component's local coclass. -/
lemma neighborhoodLocalCoclass_unique
    (β : C.neighborhoodPointSupportedCohomology)
    (hβ : β C.neighborhoodLocalClass = 1) :
    β = C.neighborhoodLocalCoclass :=
  normalizedDual_unique C.neighborhoodLocalClass_ne_zero
    C.span_neighborhoodLocalClass_eq_top β hβ

/-- Every codimension-`p` component of a smooth complex `d`-fold has an exact smooth local
coordinate package whose normalized point-supported coclass generates local cohomology. -/
lemma exists_span_neighborhoodLocalCoclass_eq_top
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) (d p : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    (hx : Order.coheight x = p) :
    ∃ C : CycleComponentSeparateLocalCoordinates X x d (d - p),
      C.neighborhoodLocalCoclass C.neighborhoodLocalClass = 1 ∧
        Submodule.span ℚ {C.neighborhoodLocalCoclass} = ⊤ := by
  obtain ⟨C, -⟩ := exists_span_neighborhoodLocalClass_eq_top X x d p hx
  exact ⟨C, C.neighborhoodLocalCoclass_apply_localClass,
    C.span_neighborhoodLocalCoclass_eq_top⟩

end AlgebraicGeometry.CycleComponentSeparateLocalCoordinates
