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

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# Canonical orientation of a cohomologically concentrated complex

The roof `K ← τ≤n K → τ≥n τ≤n K` canonically identifies a complex concentrated in
cohomological degree `n` with its actual homology object in that degree. An orientation
of this homology object therefore induces a derived orientation; no derived equivalence
or bounded replacement is supplied as data.

The explicit identity-in-degree-`n` isomorphism below adapts the construction in
Mathlib's `CochainComplex.exists_iso_single`, exposing its maps instead of choosing an
isomorphism from that existence theorem (copyright 2024 Joël Riou, Apache-2.0).
-/

@[expose] public noncomputable section

open CategoryTheory Limits HomologicalComplex

universe w v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : CochainComplex C ℤ) (n : ℤ)

set_option backward.isDefEq.respectTransparency.types false in
/-- The explicit identity-in-degree-`n` isomorphism of a termwise concentrated complex. -/
def strictSingleIso [K.IsStrictlyGE n] [K.IsStrictlyLE n] :
    K ≅ (single C (.up ℤ) n).obj (K.X n) where
  hom := mkHomToSingle (𝟙 _) (fun i (hi : i + 1 = n) ↦
    (K.isZero_of_isStrictlyGE n i (by omega)).eq_of_src _ _)
  inv := mkHomFromSingle (𝟙 _) (fun i (hi : n + 1 = i) ↦
    (K.isZero_of_isStrictlyLE n i (by omega)).eq_of_tgt _ _)
  hom_inv_id := by
    ext i
    obtain hi | rfl | hi := lt_trichotomy i n
    · apply (K.isZero_of_isStrictlyGE n i (by omega)).eq_of_src
    · simp
    · apply (K.isZero_of_isStrictlyLE n i (by omega)).eq_of_tgt
  inv_hom_id := by aesop

/-- Canonical double truncation in a single degree. -/
abbrev singleTruncation := (K.truncLE n).truncGE n

/-- Its actual homology in degree `n` is canonically that of the original complex. -/
def singleTruncationHomologyIso : (K.singleTruncation n).homology n ≅ K.homology n :=
  (isoOfQuasiIsoAt ((K.truncLE n).πTruncGE n) n).symm ≪≫
    isoOfQuasiIsoAt (K.ιTruncLE n) n

/-- The only nonzero term of the double truncation is canonically the actual homology object. -/
def singleTruncationTermIso : (K.singleTruncation n).X n ≅ K.homology n :=
  (singleObjHomologySelfIso (.up ℤ) n _).symm ≪≫
    (homologyMapIso (strictSingleIso (K.singleTruncation n) n) n).symm ≪≫
      singleTruncationHomologyIso K n

/-- Canonical single-degree model, with its term identified using actual homology maps. -/
def singleTruncationIso :
    K.singleTruncation n ≅ (single C (.up ℤ) n).obj (K.homology n) :=
  strictSingleIso (K.singleTruncation n) n ≪≫
    (single C (.up ℤ) n).mapIso (singleTruncationTermIso K n)

/-- The right leg of the canonical truncation roof. -/
def toSingleHomology : K.truncLE n ⟶ (single C (.up ℤ) n).obj (K.homology n) :=
  (K.truncLE n).πTruncGE n ≫ (singleTruncationIso K n).hom

/-- Normalization: the right leg induces exactly the same top-homology map as the left
leg. In particular, the construction introduces no scalar or generator choice. -/
@[reassoc]
theorem toSingleHomology_homology :
    homologyMap (toSingleHomology K n) n ≫
      (singleObjHomologySelfIso (.up ℤ) n _).hom = homologyMap (K.ιTruncLE n) n := by
  simp only [toSingleHomology, singleTruncationIso, Iso.trans_hom, Functor.mapIso_hom,
    homologyMap_comp, Category.assoc]
  rw [singleObjHomologySelfIso_hom_naturality]
  simp only [singleTruncationTermIso, singleTruncationHomologyIso, Iso.trans_hom,
    Iso.symm_hom, homologyMapIso_inv, Iso.hom_inv_id_assoc]
  rw [← homologyMap_comp_assoc (strictSingleIso (K.singleTruncation n) n).hom
    (strictSingleIso (K.singleTruncation n) n).inv, Iso.hom_inv_id,
    homologyMap_id, Category.id_comp]
  simp [isoOfQuasiIsoAt]

/-- Cohomological concentration implies the lower bound on the actual complex. -/
theorem isGE_of_homology_concentrated
    (h : ∀ i : ℤ, i ≠ n → IsZero (K.homology i)) : K.IsGE n := by
  rw [isGE_iff]
  exact fun i hi ↦ (exactAt_iff_isZero_homology _ _).2 (h i (ne_of_lt hi))

/-- Cohomological concentration implies the upper bound on the actual complex. -/
theorem isLE_of_homology_concentrated
    (h : ∀ i : ℤ, i ≠ n → IsZero (K.homology i)) : K.IsLE n := by
  rw [isLE_iff]
  exact fun i hi ↦ (exactAt_iff_isZero_homology _ _).2 (h i (ne_of_gt hi))

/-- The right leg of the canonical roof is a quasi-isomorphism under concentration. -/
theorem toSingleHomology_quasiIso
    (h : ∀ i : ℤ, i ≠ n → IsZero (K.homology i)) : QuasiIso (toSingleHomology K n) := by
  let := isLE_of_homology_concentrated K n h
  let : (K.truncLE n).IsGE n := by
    rw [isGE_iff]
    exact fun i hi ↦ (exactAt_iff_of_quasiIsoAt (K.ιTruncLE n) i).2
      ((exactAt_iff_isZero_homology _ _).2 (h i (ne_of_lt hi)))
  unfold toSingleHomology
  infer_instance

end CochainComplex

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  (K : CochainComplex C ℤ) (n : ℤ)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical derived comparison with the actual homology object in the unique
nonvanishing degree, constructed by inverting the canonical truncation roof. -/
def concentratedHomologyIso
    (h : ∀ i : ℤ, i ≠ n → IsZero (K.homology i)) :
    Q.obj K ≅ (singleFunctor C n).obj (K.homology n) := by
  letI := CochainComplex.isLE_of_homology_concentrated K n h
  letI : QuasiIso (CochainComplex.toSingleHomology K n) :=
    CochainComplex.toSingleHomology_quasiIso K n h
  exact (asIso (Q.map (K.ιTruncLE n))).symm ≪≫
    asIso (Q.map (CochainComplex.toSingleHomology K n))

/-- Orienting the actual unique homology object gives a derived orientation. -/
def concentratedOrientationIso
    (h : ∀ i : ℤ, i ≠ n → IsZero (K.homology i))
    {A : C} (orientation : K.homology n ≅ A) :
    Q.obj K ≅ (singleFunctor C n).obj A :=
  concentratedHomologyIso K n h ≪≫ (singleFunctor C n).mapIso orientation

set_option backward.isDefEq.respectTransparency false in
/-- The derived map is represented by the canonical truncation roof. -/
@[reassoc]
theorem concentratedHomologyIso_roof
    (h : ∀ i : ℤ, i ≠ n → IsZero (K.homology i)) :
    Q.map (K.ιTruncLE n) ≫ (concentratedHomologyIso K n h).hom =
      Q.map (CochainComplex.toSingleHomology K n) := by
  simp [concentratedHomologyIso]

set_option backward.isDefEq.respectTransparency false in
/-- The constructed derived comparison induces the identity of the actual top homology
object, under Mathlib's canonical comparison with chain-level homology. -/
@[reassoc]
theorem concentratedHomologyIso_homology
    (h : ∀ i : ℤ, i ≠ n → IsZero (K.homology i)) :
    (homologyFunctor C n).map (concentratedHomologyIso K n h).hom ≫
      (homologyFunctorFactors C n).hom.app ((single C (.up ℤ) n).obj (K.homology n)) ≫
      (singleObjHomologySelfIso (.up ℤ) n _).hom =
      (homologyFunctorFactors C n).hom.app K := by
  let := CochainComplex.isLE_of_homology_concentrated K n h
  rw [← cancel_epi ((homologyFunctor C n).map (Q.map (K.ιTruncLE n))),
    ← Functor.map_comp_assoc, concentratedHomologyIso_roof,
    homologyFunctorFactors_hom_naturality_assoc,
    CochainComplex.toSingleHomology_homology,
    homologyFunctorFactors_hom_naturality]

set_option backward.isDefEq.respectTransparency false in
/-- The derived orientation induces exactly the supplied orientation of the actual top
homology object. This equality rules out an unnoticed scalar rescaling. -/
@[reassoc]
theorem concentratedOrientationIso_homology
    (h : ∀ i : ℤ, i ≠ n → IsZero (K.homology i))
    {A : C} (orientation : K.homology n ≅ A) :
    (homologyFunctor C n).map (concentratedOrientationIso K n h orientation).hom ≫
      (homologyFunctorFactors C n).hom.app ((single C (.up ℤ) n).obj A) ≫
      (singleObjHomologySelfIso (.up ℤ) n A).hom =
      (homologyFunctorFactors C n).hom.app K ≫ orientation.hom := by
  simp only [concentratedOrientationIso, Iso.trans_hom, Functor.map_comp,
    Functor.mapIso_hom, Category.assoc]
  change (homologyFunctor C n).map (concentratedHomologyIso K n h).hom ≫
    (homologyFunctor C n).map (Q.map ((single C (.up ℤ) n).map orientation.hom)) ≫
    _ ≫ _ = _
  rw [homologyFunctorFactors_hom_naturality_assoc,
    singleObjHomologySelfIso_hom_naturality]
  exact concentratedHomologyIso_homology_assoc K n h orientation.hom

/-- Displaying the cohomological shift: concentration in degree `n` gives `A[-n]`,
because the shift convention is `K[a]^i = K^(i+a)`. -/
def concentratedOrientationShiftIso
    (h : ∀ i : ℤ, i ≠ n → IsZero (K.homology i))
    {A : C} (orientation : K.homology n ≅ A) :
    Q.obj K ≅ ((singleFunctor C 0).obj A)⟦-n⟧ :=
  concentratedOrientationIso K n h orientation ≪≫
    ((singleFunctors C).shiftIso (-n) n 0 (by omega)).symm.app A

/-- Concentration proves eligibility for `D⁺` for the actual derived object. The witness
is its cohomological bound, not an independently supplied bounded chain model. -/
def concentratedPlusObject
    (h : ∀ i : ℤ, i ≠ n → IsZero (K.homology i)) : Plus C := by
  letI := CochainComplex.isGE_of_homology_concentrated K n h
  exact ⟨Q.obj K, n, inferInstance⟩

end DerivedCategory
