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

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.SetTheory.Cardinal.NatCard

@[expose] public noncomputable section

/-!
# Tamagawa numbers of elliptic curves

For a non-archimedean local field `K`, the *Tamagawa number* is `[E(K) : E₀(K)]`, where `E₀(K)` is
the points with non-singular reduction on a minimal Weierstrass model. For a global field `K`, the
*Tamagawa product* is the finitely supported product over all non-archimedean completions.

We describe `E₀(K)` as a set using integral projective representatives, because its group structure
has not been proven, and count its distinct additive translates in `E(K)`. The local definitions
take in an integral model, which gives the usual local definitions when it is minimal.

## References

* [Silverman2009] Joseph H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts
  in Mathematics 106, Springer (2009), [doi](https://doi.org/10.1007/978-0-387-09494-6).
  Chapter VII, §§1–2 and §6: minimal equations, reduction of points, and `E(K) / E₀(K)`;
  see pp. 187–188 for the reduction map and `E₀(K)`, Proposition VII.2.1 for the subgroup and
  homomorphism properties, and Theorem VII.6.1 and Corollary VII.6.2 on p. 200.
* [LMFDB, Tamagawa number](https://www.lmfdb.org/knowledge/show/ec.tamagawa_number)
-/

namespace WeierstrassCurve.Projective

open IsDedekindDomain NumberField

/-- The points with an integral projective representative whose reduction is non-singular. -/
def nonsingularReduction {R : Type*} [CommRing R] [IsLocalRing R] (K : Type*) [CommRing K]
    [Algebra R K] (W : Projective R) : Set (W⁄K).Point :=
  {P : (W⁄K).Point | ∃ q : Fin 3 → R, P.point = ⟦(algebraMap R K <| q ·)⟧ ∧
    (W.map <| IsLocalRing.residue R).Nonsingular (IsLocalRing.residue R <| q ·)}

/-- The local Tamagawa number attached to an integral model. For a minimal model this is the
usual Tamagawa number. This is 0 if there are infinitely many distinct translates. -/
def tamagawaNumber {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (K : Type*)
    [Field K] [Algebra R K] [IsFractionRing R K] (W : Projective R) : ℕ :=
  Nat.card <| Set.range fun P : (W⁄K).Point ↦ (P + ·) '' W.nonsingularReduction K

/-- The product of local Tamagawa numbers for minimal integral models at all the non-archimedean
completions. This is 1 if infinitely many local factors differ from 1. -/
def tamagawaProduct {K : Type*} [Field K] [NumberField K] (W : Projective K) : ℕ :=
  ∏ᶠ v : HeightOneSpectrum <| RingOfIntegers K, tamagawaNumber (v.adicCompletion K)
    (W⁄(v.adicCompletion K) |>.minimal (v.adicCompletionIntegers K) |>.integralModel <|
      v.adicCompletionIntegers K)

end WeierstrassCurve.Projective
