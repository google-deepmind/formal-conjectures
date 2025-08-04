import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Orientation

scoped[EuclideanGeometry] notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open scoped EuclideanGeometry

/-- The standard basis gives us a preferred orientation in `ℝ³`.

Note: when upstreaming this to Mathlib (and generalizing to `Fin n`) one
must be careful to avoid an instance diamond with `IsEmpty.Orientation`. Presumably this can be avoided by assuming `[NeZero n]`. -/
noncomputable instance Module.orientedEuclideanSpaceFinThree : Module.Oriented ℝ ℝ³ (Fin 3) :=
  ⟨Basis.orientation <| Pi.basisFun _ _⟩

/-- Three dimensional euclidean space is three-dimensional. -/
instance fact_finrank_euclideanSpace_fin_three : Fact (Module.finrank ℝ ℝ³ = 3) :=
  ⟨finrank_euclideanSpace_fin⟩
