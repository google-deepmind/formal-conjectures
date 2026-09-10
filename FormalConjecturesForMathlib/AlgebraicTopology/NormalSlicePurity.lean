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

public import FormalConjecturesForMathlib.AlgebraicGeometry.ComplexLocalHomologyVanishing
public import FormalConjecturesForMathlib.AlgebraicTopology.RelativeHomotopyInvariance

/-!
# Actual normal-slice reduction for a product support

Contracting the tangent coordinate constructs a chain homotopy equivalence from
`(E × ℂ^c, E × (ℂ^c \ {0}))` to the normal point-complement pair. The resulting homology
and cohomology identifications therefore come from the actual projection and zero section.
They are not manufactured from one-dimensionality. The distinguished relative class is the
image of the exactly normalized `standardComplexLocalClass`.

This is the product-model computation for smooth-support purity. No claim that an arbitrary
algebraic immersion has already been flattened into this model is made here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicTopology.Singular

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℕ)

/-- The complement of the zero normal slice in a product. -/
abbrev normalSlicePair : TopPair :=
  TopPair.ofSubset (X := TopCat.of (E × (Fin c → ℂ))) {z | z.2 ≠ 0}

/-- Projection to the actual normal point-complement pair. -/
def normalSliceProjection : normalSlicePair E c ⟶ standardComplexPuncturedPair c :=
  TopPair.ofHom (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩)
    (TopCat.ofHom ⟨fun z => ⟨z.1.2, z.2⟩,
      (continuous_snd.comp continuous_subtype_val).subtype_mk _⟩) (by ext z; rfl)

/-- The zero tangent section preserves the punctured normal coordinate. -/
def normalSliceSection : standardComplexPuncturedPair c ⟶ normalSlicePair E c :=
  TopPair.ofHom (TopCat.ofHom ⟨fun z => (0, z), continuous_const.prodMk continuous_id⟩)
    (TopCat.ofHom ⟨fun z => ⟨(0, z.1), z.2⟩,
      (continuous_const.prodMk continuous_subtype_val).subtype_mk _⟩) (by ext z; rfl)

omit [NormedSpace ℝ E] in
@[simp] theorem normalSliceSection_projection :
    normalSliceSection E c ≫ normalSliceProjection E c = 𝟙 _ := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext z <;> rfl

/-- The explicit pair homotopy contracts only tangent coordinates. Its normal coordinate
is unchanged, so the complement condition holds throughout, including at the endpoints. -/
def normalSliceContraction :
    TopPair.Homotopy (normalSliceProjection E c ≫ normalSliceSection E c)
      (𝟙 (normalSlicePair E c)) where
  fst :=
    { toFun := fun tz : unitInterval × (E × (Fin c → ℂ)) =>
        ((tz.1 : ℝ) • tz.2.1, tz.2.2)
      continuous_toFun :=
        ((continuous_subtype_val.comp continuous_fst).smul
          (continuous_fst.comp continuous_snd)).prodMk (continuous_snd.comp continuous_snd)
      map_zero_left := fun z => Prod.ext (zero_smul ℝ z.1) rfl
      map_one_left := fun z => Prod.ext (one_smul ℝ z.1) rfl }
  snd :=
    { toFun := fun tz => ⟨((tz.1 : ℝ) • tz.2.1.1, tz.2.1.2), tz.2.2⟩
      continuous_toFun := (((continuous_subtype_val.comp continuous_fst).smul
        (continuous_fst.comp (continuous_subtype_val.comp continuous_snd))).prodMk
          (continuous_snd.comp (continuous_subtype_val.comp continuous_snd))).subtype_mk _
      map_zero_left := fun z => Subtype.ext (Prod.ext (zero_smul ℝ z.1.1) rfl)
      map_one_left := fun z => Subtype.ext (Prod.ext (one_smul ℝ z.1.1) rfl) }
  w := rfl

/-- The actual contraction fixes the whole zero tangent section throughout. -/
theorem normalSliceContraction_fixes_section (t : unitInterval) (z : Fin c → ℂ) :
    (normalSliceContraction E c).fst (t, (0, z)) = (0, z) :=
  Prod.ext (smul_zero (t : ℝ)) rfl

/-- Normal projection and zero section are inverse up to the actual relative prism homotopy. -/
def normalSliceRelativeChainHomotopyEquiv :
    HomotopyEquiv ((relativeChainFunctor ℚ).obj (normalSlicePair E c))
      ((relativeChainFunctor ℚ).obj (standardComplexPuncturedPair c)) where
  hom := (relativeChainFunctor ℚ).map (normalSliceProjection E c)
  inv := (relativeChainFunctor ℚ).map (normalSliceSection E c)
  homotopyHomInvId := by
    simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using
      (normalSliceContraction E c).relativeChainHomotopy (R := ℚ)
  homotopyInvHomId := Homotopy.ofEq (by
    rw [← CategoryTheory.Functor.map_comp, normalSliceSection_projection,
      CategoryTheory.Functor.map_id])

/-- The induced normal-slice isomorphism in every relative homology degree. -/
def normalSliceRelativeHomologyIso (n : ℕ) :
    RelativeHomology ℚ (normalSlicePair E c) n ≅
      RelativeHomology ℚ (standardComplexPuncturedPair c) n :=
  (normalSliceRelativeChainHomotopyEquiv E c).toHomologyIso n

@[simp] theorem normalSliceRelativeHomologyIso_hom (n : ℕ) :
    (normalSliceRelativeHomologyIso E c n).hom.hom =
      relativeHomologyMap ℚ n (normalSliceProjection E c) := rfl

@[simp] theorem normalSliceRelativeHomologyIso_inv (n : ℕ) :
    (normalSliceRelativeHomologyIso E c n).inv.hom =
      relativeHomologyMap ℚ n (normalSliceSection E c) := rfl

/-- The product pair has relative homology only in normal real dimension `2*c`, regardless
of the dimension of its tangent factor. -/
theorem normalSliceRelativeHomology_isZero_of_ne (n : ℕ) (hn : n ≠ 2 * c) :
    IsZero (RelativeHomology ℚ (normalSlicePair E c) n) :=
  (standardComplexLocalHomology_isZero_of_ne c n hn).of_iso
    (normalSliceRelativeHomologyIso E c n)

/-- The relative normal class uses the exact complex orientation, transported by the
actual zero tangent section. -/
def normalSliceClass : RelativeHomology ℚ (normalSlicePair E c) (2 * c) :=
  relativeHomologyMap ℚ (2 * c) (normalSliceSection E c) (standardComplexLocalClass c)

@[simp] theorem normalSliceProjection_class :
    relativeHomologyMap ℚ (2 * c) (normalSliceProjection E c) (normalSliceClass E c) =
      standardComplexLocalClass c := by
  change (normalSliceRelativeHomologyIso E c (2 * c)).hom.hom
    ((normalSliceRelativeHomologyIso E c (2 * c)).inv.hom (standardComplexLocalClass c)) = _
  exact ConcreteCategory.congr_hom (normalSliceRelativeHomologyIso E c (2 * c)).inv_hom_id _

theorem normalSliceClass_ne_zero : normalSliceClass E c ≠ 0 := by
  intro he
  have h := normalSliceProjection_class E c
  rw [he, map_zero] at h
  exact standardComplexLocalClass_ne_zero_for_chart c h.symm

/-- The actual normal fiber over any tangent coordinate. -/
def normalSliceSectionAt (a : E) : standardComplexPuncturedPair c ⟶ normalSlicePair E c :=
  TopPair.ofHom (TopCat.ofHom ⟨fun z => (a, z), continuous_const.prodMk continuous_id⟩)
    (TopCat.ofHom ⟨fun z => ⟨(a, z.1), z.2⟩,
      (continuous_const.prodMk continuous_subtype_val).subtype_mk _⟩) (by ext z; rfl)

/-- Moving the normal fiber in the tangent direction is an explicit pair homotopy. -/
def normalSliceSectionAtHomotopy (a : E) :
    TopPair.Homotopy (normalSliceSection E c) (normalSliceSectionAt E c a) where
  fst :=
    { toFun := fun tz : unitInterval × (Fin c → ℂ) => ((tz.1 : ℝ) • a, tz.2)
      continuous_toFun := ((continuous_subtype_val.comp continuous_fst).smul
        continuous_const).prodMk continuous_snd
      map_zero_left := fun _ => Prod.ext (zero_smul ℝ a) rfl
      map_one_left := fun _ => Prod.ext (one_smul ℝ a) rfl }
  snd :=
    { toFun := fun tz => ⟨((tz.1 : ℝ) • a, tz.2.1), tz.2.2⟩
      continuous_toFun := (((continuous_subtype_val.comp continuous_fst).smul
        continuous_const).prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _
      map_zero_left := fun _ => Subtype.ext (Prod.ext (zero_smul ℝ a) rfl)
      map_one_left := fun _ => Subtype.ext (Prod.ext (one_smul ℝ a) rfl) }
  w := rfl

/-- Every normal fiber gives the same exactly normalized class, not merely a nonzero
scalar multiple of it. -/
theorem normalSliceSectionAt_class (a : E) :
    relativeHomologyMap ℚ (2 * c) (normalSliceSectionAt E c a)
      (standardComplexLocalClass c) = normalSliceClass E c :=
  ((normalSliceSectionAtHomotopy E c a).relativeHomologyMap_apply_eq (2 * c)
    (standardComplexLocalClass c)).symm

/-- The exact normal class generates the product pair's top relative homology. This is
deduced from the constructed contraction, not used to construct it. -/
theorem span_normalSliceClass_eq_top :
    Submodule.span ℚ {normalSliceClass E c} = ⊤ := by
  let e := (normalSliceRelativeHomologyIso E c (2 * c)).symm.toLinearEquiv
  have he : e (standardComplexLocalClass c) = normalSliceClass E c := rfl
  have h := congrArg (Submodule.map e.toLinearMap)
    (span_standardComplexLocalClass_eq_top_for_chart c)
  rw [Submodule.map_span, Set.image_singleton, Submodule.map_top, LinearEquiv.range] at h
  change Submodule.span ℚ {e (standardComplexLocalClass c)} = ⊤ at h
  rwa [he] at h

/-- Normal projection gives the contravariant cohomology equivalence by dualizing its
actual homology equivalence. -/
def normalSliceRelativeCohomologyEquiv (n : ℕ) :
    RelativeCohomology ℚ (standardComplexPuncturedPair c) n ≃ₗ[ℚ]
      RelativeCohomology ℚ (normalSlicePair E c) n :=
  (normalSliceRelativeHomologyIso E c n).toLinearEquiv.dualMap

@[simp] theorem normalSliceRelativeCohomologyEquiv_apply (n : ℕ)
    (α : RelativeCohomology ℚ (standardComplexPuncturedPair c) n) :
    normalSliceRelativeCohomologyEquiv E c n α =
      relativeCohomologyMap ℚ n (normalSliceProjection E c) α := rfl

@[simp] theorem normalSliceRelativeCohomologyEquiv_evaluate_class
    (α : RelativeCohomology ℚ (standardComplexPuncturedPair c) (2 * c)) :
    normalSliceRelativeCohomologyEquiv E c (2 * c) α (normalSliceClass E c) =
      α (standardComplexLocalClass c) := by
  change α (relativeHomologyMap ℚ (2 * c) (normalSliceProjection E c)
    (normalSliceClass E c)) = _
  rw [normalSliceProjection_class]

/-- Relative cohomology is likewise concentrated in normal real dimension `2*c`. -/
theorem normalSliceRelativeCohomology_isZero_of_ne (n : ℕ) (hn : n ≠ 2 * c) :
    IsZero (ModuleCat.of ℚ (RelativeCohomology ℚ (normalSlicePair E c) n)) := by
  have := ModuleCat.subsingleton_of_isZero (normalSliceRelativeHomology_isZero_of_ne E c n hn)
  exact ModuleCat.isZero_of_subsingleton _

end AlgebraicTopology.Singular
