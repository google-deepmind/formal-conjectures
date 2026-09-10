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

public import FormalConjecturesForMathlib.AlgebraicTopology.LocalFundamentalClass
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

/-- List the real and imaginary part of each complex coordinate consecutively. -/
def complexCoordinatesToReal (p : ℕ) (z : Fin p → ℂ) : StandardRealModel (p * 2) := fun k =>
  let jk := finProdFinEquiv.symm k
  ![(z jk.1).re, (z jk.1).im] jk.2

/-- Reassemble consecutive pairs of real coordinates into complex coordinates. -/
def realCoordinatesToComplex (p : ℕ) (x : StandardRealModel (p * 2)) (j : Fin p) : ℂ :=
  ⟨x (finProdFinEquiv (j, 0)), x (finProdFinEquiv (j, 1))⟩

/-- Complex coordinates followed by real-coordinate listing are continuous. -/
lemma continuous_complexCoordinatesToReal (p : ℕ) : Continuous (complexCoordinatesToReal p) := by
  apply continuous_pi
  intro k
  generalize h : finProdFinEquiv.symm k = jk
  rcases jk with ⟨j, l⟩
  fin_cases l
  · simpa [complexCoordinatesToReal, h, Function.comp_def, Complex.reCLM_apply] using
      Complex.reCLM.continuous.comp
      (continuous_apply j : Continuous (fun z : Fin p → ℂ => z j))
  · simpa [complexCoordinatesToReal, h, Function.comp_def, Complex.imCLM_apply] using
      Complex.imCLM.continuous.comp
      (continuous_apply j : Continuous (fun z : Fin p → ℂ => z j))

/-- Reassembling real coordinate pairs into complex coordinates is continuous. -/
lemma continuous_realCoordinatesToComplex (p : ℕ) : Continuous (realCoordinatesToComplex p) := by
  apply continuous_pi
  intro j
  have hp : Continuous (fun x : StandardRealModel (p * 2) =>
      (x (finProdFinEquiv (j, 0)), x (finProdFinEquiv (j, 1)))) :=
    (continuous_apply (finProdFinEquiv (j, 0))).prodMk
      (continuous_apply (finProdFinEquiv (j, 1)))
  have he := Complex.equivRealProdCLM.symm.continuous.comp hp
  convert he using 1
  funext x
  apply Complex.ext <;> simp [realCoordinatesToComplex, Complex.equivRealProdCLM_symm_apply]

/-- Reassembling the listed coordinates recovers the original complex vector. -/
lemma realCoordinatesToComplex_complexCoordinatesToReal (p : ℕ) (z : Fin p → ℂ) :
    realCoordinatesToComplex p (complexCoordinatesToReal p z) = z := by
  apply funext
  intro j
  apply Complex.ext <;> simp [realCoordinatesToComplex, complexCoordinatesToReal]

/-- Listing the coordinates of a reassembled complex vector recovers the real vector. -/
lemma complexCoordinatesToReal_realCoordinatesToComplex (p : ℕ)
    (x : StandardRealModel (p * 2)) :
    complexCoordinatesToReal p (realCoordinatesToComplex p x) = x := by
  ext k
  obtain ⟨⟨j, l⟩, rfl⟩ := finProdFinEquiv.surjective k
  fin_cases l <;> simp [complexCoordinatesToReal, realCoordinatesToComplex]

/-- The orientation-ordered homeomorphism from complex coordinate space to real coordinate space. -/
def complexRealHomeomorph (p : ℕ) : (Fin p → ℂ) ≃ₜ StandardRealModel (p * 2) where
  toFun := complexCoordinatesToReal p
  invFun := realCoordinatesToComplex p
  left_inv := realCoordinatesToComplex_complexCoordinatesToReal p
  right_inv := complexCoordinatesToReal_realCoordinatesToComplex p
  continuous_toFun := continuous_complexCoordinatesToReal p
  continuous_invFun := continuous_realCoordinatesToComplex p

/-- Complex coordinate space paired with the complement of its origin. -/
abbrev standardComplexPuncturedPair (p : ℕ) : TopPair :=
  TopPair.ofSubset (X := TopCat.of (Fin p → ℂ)) ({0}ᶜ : Set (Fin p → ℂ))

/-- The inverse coordinate homeomorphism restricted to the punctured spaces. -/
def puncturedRealToComplex (p : ℕ) :
    ({0}ᶜ : Set (StandardRealModel (p * 2))) → ({0}ᶜ : Set (Fin p → ℂ)) :=
  fun x => ⟨complexRealHomeomorph p |>.symm x.1, by
    intro hz
    apply x.2
    calc
      x.1 = complexRealHomeomorph p (complexRealHomeomorph p |>.symm x.1) :=
        (complexRealHomeomorph p).apply_symm_apply x.1 |>.symm
      _ = complexRealHomeomorph p 0 := congrArg (complexRealHomeomorph p) hz
      _ = 0 := by
        funext k
        change ![0, 0] (finProdFinEquiv.symm k).2 = 0
        generalize (finProdFinEquiv.symm k).2 = l
        fin_cases l <;> rfl⟩

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
  fun z => ⟨complexRealHomeomorph p z.1, by
    intro hz
    apply z.2
    calc
      z.1 = (complexRealHomeomorph p).symm (complexRealHomeomorph p z.1) :=
        (complexRealHomeomorph p).symm_apply_apply z.1 |>.symm
      _ = (complexRealHomeomorph p).symm 0 :=
        congrArg (complexRealHomeomorph p).symm hz
      _ = 0 := by
        funext j
        apply Complex.ext <;> simp [complexRealHomeomorph, realCoordinatesToComplex]⟩

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
