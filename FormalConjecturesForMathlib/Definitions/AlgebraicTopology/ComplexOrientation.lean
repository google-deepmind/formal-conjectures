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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.LocalFundamentalClass
public import FormalConjecturesForMathlib.Lemmas.LinearAlgebra.ComplexOrientation
public import Mathlib.Analysis.Complex.Basic

/-!
# The standard complex local class

This file identifies `ℂ^p` with an ordered real coordinate space by listing the real and imaginary
part of each complex coordinate consecutively. It transports the explicit standard local cycle to
`H_{2p}(ℂ^p, ℂ^p ∖ {0}; ℚ)`. Thus the complex orientation is constructed from complex coordinates
rather than supplied as data.
-/

open CategoryTheory

@[expose] public noncomputable section

namespace AlgebraicTopology.Singular

/-- The orientation-ordered homeomorphism from complex coordinate space to real coordinate space.

This is the coordinate map of `Complex.piBasisOneI`, so it lists the real and imaginary part of
each complex coordinate consecutively; continuity in both directions comes from
`Basis.equivFunL`. -/
def complexRealHomeomorph (p : ℕ) : (Fin p → ℂ) ≃ₜ StandardRealModel (p * 2) :=
  (Complex.piCoordCLE p).toHomeomorph

/-- Complex coordinate space paired with the complement of its origin. -/
abbrev standardComplexPuncturedPair (p : ℕ) : TopPair :=
  TopPair.ofSubset (X := TopCat.of (Fin p → ℂ)) ({0}ᶜ : Set (Fin p → ℂ))

/-- The inverse coordinate homeomorphism restricted to the punctured spaces. -/
def puncturedRealToComplex (p : ℕ) :
    ({0}ᶜ : Set (StandardRealModel (p * 2))) → ({0}ᶜ : Set (Fin p → ℂ)) :=
  fun x => ⟨(Complex.piCoordCLE p).symm x.1,
    fun hz => x.2 ((Complex.piCoordCLE p).symm.map_eq_zero_iff.mp hz)⟩

/-- The restricted inverse coordinate map is continuous. -/
lemma continuous_puncturedRealToComplex (p : ℕ) : Continuous (puncturedRealToComplex p) :=
  ((complexRealHomeomorph p).symm.continuous.comp continuous_subtype_val).subtype_mk _

/-- The inverse coordinate homeomorphism as a morphism of punctured pairs. -/
def standardRealToComplexPair (p : ℕ) :
    standardPuncturedPair (p * 2) ⟶ standardComplexPuncturedPair p :=
  TopPair.ofHom
    (TopCat.ofHom ⟨(complexRealHomeomorph p).symm,
      (complexRealHomeomorph p).symm.continuous⟩)
    (TopCat.ofHom ⟨puncturedRealToComplex p, continuous_puncturedRealToComplex p⟩)
    (by ext x; rfl)

/-- The complex-to-real coordinate homeomorphism restricted to the punctured spaces. -/
def puncturedComplexToReal (p : ℕ) :
    ({0}ᶜ : Set (Fin p → ℂ)) → ({0}ᶜ : Set (StandardRealModel (p * 2))) :=
  fun z => ⟨Complex.piCoordCLE p z.1,
    fun hz => z.2 ((Complex.piCoordCLE p).map_eq_zero_iff.mp hz)⟩

/-- The restricted complex-to-real coordinate map is continuous. -/
lemma continuous_puncturedComplexToReal (p : ℕ) : Continuous (puncturedComplexToReal p) :=
  ((complexRealHomeomorph p).continuous.comp continuous_subtype_val).subtype_mk _

/-- The coordinate homeomorphism as a morphism from the complex pair to the real pair. -/
def standardComplexToRealPair (p : ℕ) :
    standardComplexPuncturedPair p ⟶ standardPuncturedPair (p * 2) :=
  TopPair.ofHom
    (TopCat.ofHom ⟨complexRealHomeomorph p, (complexRealHomeomorph p).continuous⟩)
    (TopCat.ofHom ⟨puncturedComplexToReal p, continuous_puncturedComplexToReal p⟩)
    (by ext z; rfl)

/-- The isomorphism of punctured pairs induced by ordered real and imaginary coordinates. -/
def standardComplexRealPairIso (p : ℕ) :
    standardComplexPuncturedPair p ≅ standardPuncturedPair (p * 2) where
  hom := standardComplexToRealPair p
  inv := standardRealToComplexPair p
  hom_inv_id := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext z
      exact Subtype.ext ((complexRealHomeomorph p).left_inv z.1)
    · ext z
      exact (complexRealHomeomorph p).left_inv z
  inv_hom_id := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext x
      exact Subtype.ext ((complexRealHomeomorph p).right_inv x.1)
    · ext x
      exact (complexRealHomeomorph p).right_inv x

/-- The induced isomorphism between complex and real local homology. -/
def standardComplexRealRelativeHomologyIso (p : ℕ) :
    RelativeHomology ℚ (standardComplexPuncturedPair p) (p * 2) ≅
      RelativeHomology ℚ (standardPuncturedPair (p * 2)) (p * 2) :=
  (relativeHomologyFunctor ℚ (p * 2)).mapIso (standardComplexRealPairIso p)

/-- The standard complex local class obtained from the explicit real local cycle. -/
def standardComplexLocalClass (p : ℕ) :
    RelativeHomology ℚ (standardComplexPuncturedPair p) (2 * p) :=
  (Nat.mul_comm p 2) ▸
    (standardComplexRealRelativeHomologyIso p).inv.hom (standardLocalClass (p * 2))

end AlgebraicTopology.Singular
