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

public import FormalConjecturesForMathlib.RepresentationTheory.Homological.ContCohomology.Sha
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-!
# The Tate–-Shafarevich group of an elliptic curve over a number field

The non-singular points over an algebraic closure of a field `K` carry a discrete Galois
representation. For a number field, the *Tate–Shafarevich group* is the intersection of the kernels
of restriction to all infinite and finite completions, where finite places are indexed by the
non-zero prime ideals of the ring of integers of `K`. The coefficient module remains the geometric
points over the separable closure of `K`, with its action restricted to each local Galois group.

## References

* [Silverman2009] Joseph H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts
  in Mathematics 106, Springer (2009), [doi](https://doi.org/10.1007/978-0-387-09494-6).
  Chapter X, §4, pp. 331–333, especially the definition on p. 332, gives the classical
  Tate–-Shafarevich group over a number field, using local geometric points.
* [J. S. Milne, Arithmetic Duality Theorems](https://www.jmilne.org/math/Books/ADTnot.pdf)
* [J. S. Milne, Elliptic Curves](https://www.jmilne.org/math/Books/EC2.pdf), 2nd ed., Chapter IV,
  Remark 1.11, p. 111, explains the use of a separable closure over imperfect fields.
-/

@[expose] public section

namespace WeierstrassCurve.Affine

open ContinuousCohomology IsDedekindDomain NumberField

variable {K : Type*} [Field K] (W : Affine K)

/-- The geometric non-singular points as a topological space. -/
local instance : TopologicalSpace (W⁄(AlgebraicClosure K)).Point := ⊥

/-- The geometric non-singular points equipped with the discrete topology. -/
local instance : DiscreteTopology (W⁄(AlgebraicClosure K)).Point := ⟨rfl⟩

open scoped Classical in
/-- The natural Galois action on geometric non-singular points with their discrete topology.

This uses `AlgebraicClosure K` to match `Field.absoluteGaloisGroup`. For number fields, which are
perfect, an algebraic closure is also a separable closure. Over an imperfect field, the coefficient
module for the usual Galois cohomology of an elliptic curve should use `SeparableClosure K` instead.

TODO: use `SeparableClosure K` for the coefficient field when the API for absolute Galois groups
supports this directly. The automorphism group of the algebraic closure itself gives the usual
absolute Galois group by restriction to the separable closure. -/
noncomputable def galoisRepresentation : TopRep ℤ <| Field.absoluteGaloisGroup K := .of <|
  .ofMonoidHom { toFun σ := { __ := (Affine.Point.map (W' := W) σ.toAlgHom).toIntLinearMap
                              cont := continuous_of_discreteTopology }
                 map_one' := by ext P; cases P <;> rfl
                 map_mul' _ _ := by ext P; cases P <;> rfl }


/-- The Tate--Shafarevich subgroup of the first continuous Galois cohomology group over a number
field, using restriction to every infinite and finite completion. -/
noncomputable def tateShafarevich [NumberField K] :
    AddSubgroup <| continuousCohomology 1 W.galoisRepresentation :=
  tateSha (fun v : InfinitePlace K ↦ v.Completion) W.galoisRepresentation 1 ⊓
    tateSha (fun v : HeightOneSpectrum <| 𝓞 K ↦ v.adicCompletion K) W.galoisRepresentation 1

end WeierstrassCurve.Affine
