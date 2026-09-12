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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.SingularLocusDimension
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

end AlgebraicGeometry.ComplexPoint
