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
/- The adapted Tau Ceti definitions are copyright (c) 2026 The Tau Ceti contributors,
released under the Apache License, Version 2.0. -/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.NumberTheory.Height.Basic
public import Mathlib.Topology.Order.Basic

@[expose] public noncomputable section

/-!
# Heights and the regulator of an elliptic curve

Let `K` be a field with admissible absolute values. The *canonical height* is a quadratic form,
defined as the limit of `4⁻ⁿhₓ(2ⁿP)` as `n → ∞`. Here, `hₓ(P)` is the *naïve height*, which is the
logarithm of the maximum of the absolute numerator and denominator of the `x`-coordinate. The
*Néron--Tate pairing* is the bilinear pairing associated to the canonical height. The *regulator* is
the absolute determinant of the Gram matrix of the *Néron--Tate pairing* on `E(K)` modulo torsion.

These definitions are adapted from the Apache-2.0-licensed Tau Ceti files
`MordellWeil/NaiveHeight.lean`, `CanonicalHeight.lean`, `MordellWeil/PointModTorsion.lean`,
and `MordellWeil/Regulator.lean`. Over `ℚ`, the canonical height here is twice Tau Ceti's height,
so a rank-`r` regulator is `2ʳ` times Tau Ceti's regulator.

## References

* [Silverman2009] Joseph H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts
  in Mathematics 106, Springer (2009), [doi](https://doi.org/10.1007/978-0-387-09494-6).
  Chapter VIII, §§5–6 and §9: heights, the canonical pairing, and the elliptic regulator;
  see especially pp. 252–253 and Remark VIII.9.8 for the relative normalization.
* [Tau Ceti regulator](https://github.com/TauCetiProject/TauCeti/pull/5692)
* [LMFDB canonical height](https://www.lmfdb.org/knowledge/show/ec.q.canonical_height)
* [LMFDB regulator](https://www.lmfdb.org/knowledge/show/ec.q.regulator)
* [SageMath heights and regulators over number fields][sage-regulator](https://doc.sagemath.org/html/en/reference/arithmetic_curves/sage/schemes/elliptic_curves/ell_number_field.html)
-/

namespace WeierstrassCurve.Affine.Point

variable {K : Type*} [DecidableEq K] [Field K] [Height.AdmissibleAbsValues K] {W : Affine K}
  (P Q : W.Point)

/-- The logarithmic height `hₓ` of the `x`-coordinate with value zero at infinity. -/
def naiveHeight : W.Point → ℝ
  | .zero => 0
  | .some x .. => Height.logHeight₁ x

/-- The canonical height `lim_n 4⁻ⁿhₓ(2ⁿP)` in terms of the logarithmic height `hₓ`. -/
def canonicalHeight : ℝ := Filter.atTop.limUnder fun n : ℕ ↦ (2 ^ n • P).naiveHeight / 4 ^ n

/-- The Néron--Tate height pairing, defined by polarisation of the canonical height. -/
def neronTatePairing : ℝ := ((P + Q).canonicalHeight - P.canonicalHeight - Q.canonicalHeight) / 2

/-- The Gram matrix of the Néron--Tate height pairing on any family of `K`-rational points. -/
def neronTateMatrix {ι : Type*} (P : ι → W.Point) : Matrix ι ι ℝ :=
  @Matrix.gram _ _ ℝ ⟨neronTatePairing⟩ P

variable (W) in
/-- The absolute determinant of the height pairing on a finite basis of `E(K)` modulo torsion.
For number fields with their standard height instance, this is the non-normalised regulator. -/
def regulator [Module.Finite ℤ (W.Point ⧸ Submodule.torsion ℤ W.Point)] : ℝ :=
  |(neronTateMatrix (Quotient.out ∘ Module.finBasis ℤ (W.Point ⧸ Submodule.torsion ℤ W.Point))).det|

end WeierstrassCurve.Affine.Point
