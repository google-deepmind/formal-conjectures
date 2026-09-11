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

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Restriction to the smooth locus

This file proves that restricting a locally finitely presented scheme morphism to its smooth
locus gives a smooth morphism.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

/-- A locally finitely presented morphism is smooth after restricting its source to the smooth
locus. -/
lemma Scheme.Hom.smooth_restrict_smoothLocus
    (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    Smooth (f.smoothLocus.ι ≫ f) := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
  ext x
  simp

end AlgebraicGeometry
