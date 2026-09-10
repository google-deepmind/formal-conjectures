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

public import FormalConjecturesForMathlib.AlgebraicGeometry.SingularLocusDimension

import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Complex points of the constructed smooth decomposition

The finite algebraic decomposition induces an actual partition of complex-point sets into
the images of smooth complex schemes. The images are analytically locally closed. The
lifting assertion follows from the existing equivalence between complex points and closed
scheme points; it is not a supplied parametrization of a stratum.

No analytic triangulation, homology-dimension theorem, or frontier condition is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ))) {Y : Over (Spec (.of ℂ))}

local instance smoothStratificationAnalyticTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

/-- Forgetting a complex point to its underlying Zariski point is continuous for the actual
analytic topology. -/
theorem continuous_underlying_to_zariski :
    Continuous (Point.underlying : ComplexPoint X → X.left) := by
  rw [continuous_def]
  exact fun S hS => Point.isOpen_overOpen ⟨S, hS⟩

/-- The complex points of a locally closed subscheme map onto exactly the complex points
whose underlying scheme point belongs to its range. -/
theorem range_map_of_isImmersion (i : Y ⟶ X)
    [IsImmersion i.left] [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] :
    Set.range (Point.map i) =
      (Point.underlying : ComplexPoint X → X.left) ⁻¹' Set.range i.left := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w.underlying, rfl⟩
  · rintro ⟨y, hy⟩
    have hyclosed : IsClosed ({y} : Set Y.left) := by
      have h := ((pointEquivClosedPoint X.hom) ⟨z.left, z.w⟩).2.preimage i.left.continuous
      change IsClosed (i.left ⁻¹' ({z.underlying} : Set X.left)) at h
      have he : i.left ⁻¹' ({z.underlying} : Set X.left) = {y} := by
        rw [← hy]
        ext a
        exact i.left.isEmbedding.injective.eq_iff
      rwa [he] at h
    let p := (pointEquivClosedPoint Y.hom).symm ⟨y, hyclosed⟩
    let w : ComplexPoint Y := Over.homMk p.1 p.2
    refine ⟨w, ?_⟩
    apply Over.OverMorphism.ext
    have heq :
        (⟨(Point.map i w).left, (Point.map i w).w⟩ :
          {q : Spec (.of ℂ) ⟶ X.left // q ≫ X.hom = 𝟙 _}) = ⟨z.left, z.w⟩ := by
      apply (pointEquivClosedPoint X.hom).injective
      apply Subtype.ext
      change i.left w.underlying = z.underlying
      have hw : w.underlying = y :=
        congrArg Subtype.val
          ((pointEquivClosedPoint Y.hom).apply_symm_apply ⟨y, hyclosed⟩)
      rw [hw]
      exact hy
    exact congrArg Subtype.val heq

/-- Each algebraic locally closed immersion has analytically locally closed complex-point
image. This asserts the image topology property, not yet a homeomorphism onto that image. -/
theorem isLocallyClosed_range_map_of_isImmersion (i : Y ⟶ X)
    [IsImmersion i.left] [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] :
    IsLocallyClosed (Set.range (Point.map i)) := by
  rw [range_map_of_isImmersion X i]
  exact i.left.isLocallyClosed_range.preimage (continuous_underlying_to_zariski X)

variable [LocallyOfFiniteType X.hom] [NoetherianSpace X.left]

/-- The inclusion of a reduced smooth stratum, bundled over the complex base. -/
def reducedClosedSmoothPieceMap (T : Closeds X.left) :
    Over.mk (reducedClosedSmoothPieceι X.hom T ≫ X.hom) ⟶ X :=
  Over.homMk (reducedClosedSmoothPieceι X.hom T) rfl

instance reducedClosedSmoothPieceMap_isImmersion (T : Closeds X.left) :
    IsImmersion (reducedClosedSmoothPieceMap X T).left := by
  change IsImmersion (reducedClosedSmoothPieceι X.hom T)
  infer_instance

instance reducedClosedSmoothPiece_locallyOfFiniteType (T : Closeds X.left) :
    LocallyOfFiniteType (Over.mk (reducedClosedSmoothPieceι X.hom T ≫ X.hom)).hom := by
  change LocallyOfFiniteType (reducedClosedSmoothPieceι X.hom T ≫ X.hom)
  infer_instance

/-- The actual smooth pieces cover precisely the complex points on the given closed set. -/
theorem reducedSmoothStratification_complexPoints_covers (S : Closeds X.left)
    (z : ComplexPoint X) :
    (∃ T ∈ reducedSmoothStratification X.hom S,
      z ∈ Set.range (Point.map (reducedClosedSmoothPieceMap X T))) ↔
        z.underlying ∈ S := by
  simp only [range_map_of_isImmersion X, Set.mem_preimage]
  exact reducedSmoothStratification_covers X.hom S z.underlying

/-- The analytic images of the constructed smooth pieces are pairwise disjoint. -/
theorem reducedSmoothStratification_complexPoints_pairwiseDisjoint (S : Closeds X.left) :
    (reducedSmoothStratification X.hom S).Pairwise (fun T U =>
      Disjoint
        (Set.range (Point.map (reducedClosedSmoothPieceMap X T)))
        (Set.range (Point.map (reducedClosedSmoothPieceMap X U)))) := by
  apply (reducedSmoothStratification_pairwiseDisjoint X.hom S).imp
  intro T U hTU
  rw [range_map_of_isImmersion X (reducedClosedSmoothPieceMap X T),
    range_map_of_isImmersion X (reducedClosedSmoothPieceMap X U)]
  exact hTU.preimage Point.underlying

end AlgebraicGeometry.ComplexPoint
