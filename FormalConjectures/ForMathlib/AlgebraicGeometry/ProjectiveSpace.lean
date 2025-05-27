import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.RingTheory.MvPolynomial.Homogeneous

universe u v u' v' w


open CategoryTheory Limits MvPolynomial AlgebraicGeometry

variable (n : Type v) (S : Scheme.{max u v})

local notation3 "ℤ[" n "]" => homogeneousSubmodule n ℤ
local notation3 "ℤ[" n "].{" u "," v "}" => homogeneousSubmodule n (ULift.{max u v} ℤ)

attribute [local instance] MvPolynomial.gradedAlgebra

/--
The projective space over a scheme `S`, with homogeneous coordinates indexed by `n`
-/
noncomputable def ProjectiveSpace : Scheme.{max u v} :=
  pullback (terminal.from S) (terminal.from (Proj ℤ[n].{u, v}))

/-- `ℙ(n; S)` is the affine `S` indexed by `n` -/
scoped [AlgebraicGeometry] notation "ℙ("n"; "S")" => ProjectiveSpace n S
