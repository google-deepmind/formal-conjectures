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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.CycleComponentLocalGenerator

import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.CycleComponentClosedPointDimension
import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.ProjectiveAnalytificationHausdorff
import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.ChartLocalFundamentalClassGenerator
import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.LocalFundamentalClassGenerator
import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.PuncturedEuclideanFundamentalClass

/-!
# Local dual classes on cycle components

The local fundamental class obtained from exact coordinates on the smooth locus of a cycle
component is nonzero.  Since it generates local homology, there is a unique local cohomology
class evaluating to one on it, and that normalized dual class generates cohomology supported at
the chosen point.

This is intrinsic purity on the smooth component neighborhood.  It does not yet give ambient
purity in codimension `p`: that requires a Thom or Gysin comparison between the intrinsic local
homology in degree `2 * (d - p)` and ambient cohomology supported on the component in degree
`2 * p`.
-/

@[expose] public noncomputable section

open CategoryTheory Topology

namespace AlgebraicTopology.Singular

variable {R M : Type*} [Field R] [AddCommGroup M] [Module R M]

/-- The normalized dual of a nonzero vector. -/
def normalizedDual (z : M) (hz : z ≠ 0) : Module.Dual R M :=
  Classical.choose (Module.Projective.exists_dual_eq_one R hz)

@[simp]
lemma normalizedDual_apply_self (z : M) (hz : z ≠ 0) :
    (normalizedDual (R := R) z hz) z = (1 : R) :=
  Classical.choose_spec (Module.Projective.exists_dual_eq_one R hz)

/-- Two one-dimensional vector spaces with specified normalized generators are canonically
linearly equivalent by sending the first generator to the second. -/
def linearEquivOfNormalizedGenerators
    {N : Type*} [AddCommGroup N] [Module R N]
    (x : M) (hx : x ≠ 0) (hxspan : Submodule.span R {x} = ⊤)
    (y : N) (hy : y ≠ 0) (hyspan : Submodule.span R {y} = ⊤) :
    M ≃ₗ[R] N := by
  let f : M →ₗ[R] N :=
    (LinearMap.toSpanSingleton R N y).comp (normalizedDual x hx)
  let g : N →ₗ[R] M :=
    (LinearMap.toSpanSingleton R M x).comp (normalizedDual y hy)
  apply LinearEquiv.ofLinearMap f g
  · apply LinearMap.ext
    intro n
    obtain ⟨a, rfl⟩ := (Submodule.span_singleton_eq_top_iff R y).mp hyspan n
    simp [f, g, normalizedDual_apply_self]
  · apply LinearMap.ext
    intro m
    obtain ⟨a, rfl⟩ := (Submodule.span_singleton_eq_top_iff R x).mp hxspan m
    simp [f, g, normalizedDual_apply_self]

/-- The oriented standard complex local class is nonzero in every complex dimension. -/
lemma standardComplexLocalClass_ne_zero (n : ℕ) :
    standardComplexLocalClass n ≠ 0 := by
  rw [standardComplexLocalClass_ne_zero_iff]
  by_cases hn : n = 0
  · subst n
    exact standardLocalClass_zero_ne_zero
  · exact standardLocalClass_ne_zero_of_pos (n * 2) (Nat.mul_pos (Nat.pos_of_ne_zero hn) (by
      norm_num))

end AlgebraicTopology.Singular

namespace AlgebraicGeometry.CycleComponentSeparateLocalCoordinates

open AlgebraicTopology.Singular

noncomputable local instance {Y : Over (Spec ↧ℂ)} :
    TopologicalSpace (ComplexPoint Y) := Point.analyticTopology

variable {d n : ℕ} {X : Over (Spec ↧ℂ)} [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom] {x : X.left}
  [SmoothOfRelativeDimension d X.hom]
  (C : CycleComponentSeparateLocalCoordinates X x d n)

/-- The local homology class transported from the exact component chart is nonzero. -/
lemma neighborhoodLocalClass_ne_zero : C.neighborhoodLocalClass ≠ 0 := by
  let : IsAffine C.neighborhoodScheme.left :=
    C.componentNeighborhood_isAffine
  let : T2Space
      (ComplexPoint C.neighborhoodScheme) :=
    ComplexPoint.t2Space_of_isAffine C.neighborhoodScheme
  have hinjective : Function.Injective C.neighborhoodLocalHomologyMap :=
    (chartModelEmbedding_relativeHomologyMap_bijective
      n C.neighborhoodProjectionChart C.neighborhoodPoint
        C.neighborhoodPoint_mem_projectionChart_source).1
  intro hzero
  apply standardComplexLocalClass_ne_zero n
  apply hinjective
  simpa only [neighborhoodLocalClass, map_zero] using hzero

/-- Cohomology of the component neighborhood supported at its selected smooth point. -/
abbrev neighborhoodPointSupportedCohomology :=
  CohomologyWithSupport ℚ
    (TopCat.of (ComplexPoint C.neighborhoodScheme))
    {C.neighborhoodPoint} (2 * n)

/-- The unique local cohomology class normalized to evaluate to one on the transported local
fundamental class. -/
def neighborhoodLocalCoclass : C.neighborhoodPointSupportedCohomology :=
  normalizedDual C.neighborhoodLocalClass C.neighborhoodLocalClass_ne_zero

end AlgebraicGeometry.CycleComponentSeparateLocalCoordinates
