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

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Orientation

scoped[EuclideanGeometry] notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open scoped EuclideanGeometry

/-- The standard basis gives us a preferred orientation in `ℝ³`.

Note: when upstreaming this to Mathlib (and generalizing to `Fin n`) one
must be careful to avoid an instance diamond with `IsEmpty.Orientation`.
Presumably this can be avoided by assuming `[NeZero n]`. -/
noncomputable instance Module.orientedEuclideanSpaceFinThree : Module.Oriented ℝ ℝ³ (Fin 3) :=
  ⟨Basis.orientation <| Pi.basisFun _ _⟩

/-- Three dimensional euclidean space is three-dimensional. -/
instance fact_finrank_euclideanSpace_fin_three : Fact (Module.finrank ℝ ℝ³ = 3) :=
  ⟨finrank_euclideanSpace_fin⟩
