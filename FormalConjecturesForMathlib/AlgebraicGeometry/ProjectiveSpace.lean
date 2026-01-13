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
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.RingTheory.MvPolynomial.Homogeneous

-- The contents of this file will be in mathlib as of #26061 which should be merged in 4.21 or 4.22.

universe u v
open CategoryTheory Limits MvPolynomial AlgebraicGeometry

variable (n : Type v) (S : Scheme.{max u v})

local notation "ℤ[" n "]" => homogeneousSubmodule n ℤ
local notation3 "ℤ[" n "].{" u "," v "}" => homogeneousSubmodule n (ULift.{max u v} ℤ)

attribute [local instance] MvPolynomial.gradedAlgebra

/--
The projective space over a scheme `S`, with homogeneous coordinates indexed by `n`
-/
noncomputable def ProjectiveSpace : Scheme.{max u v} :=
  pullback (terminal.from S) (terminal.from (Proj ℤ[n].{u, v}))

/-- `ℙ(n; S)` is the affine `S` indexed by `n` -/
scoped [AlgebraicGeometry] notation "ℙ("n"; "S")" => ProjectiveSpace n S
