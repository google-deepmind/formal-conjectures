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

public import Mathlib.Algebra.Homology.Embedding.StupidTrunc

/-!
# Inclusion of a stupid truncation

For an embedding of complex shapes whose image is closed under the next differential, the stupid
truncation is canonically a subcomplex. This file constructs its inclusion into the original
complex and proves naturality. It supplies the inclusion noted as missing in Mathlib's
`Embedding.StupidTrunc`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

variable {I J : Type*} {c : ComplexShape I} {c' : ComplexShape J}

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
variable (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsTruncGE]

open scoped Classical in
/-- The component of the inclusion from a stupid truncation. It is the canonical isomorphism in
the image of the embedding and the zero morphism outside that image. -/
def stupidTruncInclusionApp (j : J) : (K.stupidTrunc e).X j ⟶ K.X j :=
  if h : ∃ i, e.f i = j then
    (K.stupidTruncXIso e h.choose_spec).hom
  else 0

lemma stupidTruncInclusionApp_eq {i : I} {j : J} (h : e.f i = j) :
    stupidTruncInclusionApp K e j = (K.stupidTruncXIso e h).hom := by
  have hj : ∃ k, e.f k = j := ⟨i, h⟩
  have hchoice : hj.choose = i := e.injective_f (hj.choose_spec.trans h.symm)
  grind [stupidTruncInclusionApp]

set_option backward.isDefEq.respectTransparency false in
lemma stupidTrunc_d_comp_XIso {i j : I} (_hij : c'.Rel (e.f i) (e.f j)) :
    (K.stupidTrunc e).d (e.f i) (e.f j) ≫
        (K.stupidTruncXIso e (i := j) rfl).hom =
      (K.stupidTruncXIso e (i := i) rfl).hom ≫ K.d (e.f i) (e.f j) := by
  simp [stupidTruncXIso, stupidTrunc, extend_d_eq (K.restriction e) e rfl rfl]

/-- The canonical inclusion of a stupid truncation whose retained degrees are closed under the
next differential. -/
def stupidTruncInclusion : K.stupidTrunc e ⟶ K where
  f j := stupidTruncInclusionApp K e j
  comm' i' j' hij := by
    by_cases hi : ∃ i, e.f i = i'
    · obtain ⟨i, hi⟩ := hi
      obtain ⟨j, hj⟩ := e.mem_next (hi ▸ hij)
      rw [stupidTruncInclusionApp_eq K e hi, stupidTruncInclusionApp_eq K e hj]
      subst i' j'
      exact (stupidTrunc_d_comp_XIso K e hij).symm
    · exact (K.isZero_stupidTrunc_X e i' (by simpa using hi)).eq_of_src _ _

@[simp] lemma stupidTruncInclusion_f {i : I} {j : J} (h : e.f i = j) :
    (stupidTruncInclusion K e).f j = (K.stupidTruncXIso e h).hom :=
  stupidTruncInclusionApp_eq K e h

/-- The inclusion of the stupid truncation is an isomorphism when the original complex is already
strictly supported on the retained degrees. -/
noncomputable instance stupidTruncInclusion_isIso [K.IsStrictlySupported e] :
    IsIso (stupidTruncInclusion K e) := by
  let componentIsIso (j : J) : IsIso ((stupidTruncInclusion K e).f j) := by
    by_cases hj : ∃ i, e.f i = j
    · obtain ⟨i, hi⟩ := hj
      rw [stupidTruncInclusion_f K e hi]
      infer_instance
    · exact IsZero.isIso (K.isZero_stupidTrunc_X e j (by simpa using hj))
        (K.isZero_X_of_isStrictlySupported e j (by simpa using hj)) _
  exact @Hom.isIso_of_components J C _ _ c' _ _
    (stupidTruncInclusion K e) componentIsIso

variable {K} {L : HomologicalComplex C c'}

lemma stupidTruncMap_comp_stupidTruncInclusion (f : K ⟶ L) :
    stupidTruncMap f e ≫ stupidTruncInclusion L e =
      stupidTruncInclusion K e ≫ f := by
  ext j
  by_cases hj : ∃ i, e.f i = j
  · obtain ⟨i, hi⟩ := hj
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      stupidTruncInclusion_f L e hi, stupidTruncInclusion_f K e hi,
      stupidTruncMap_stupidTruncXIso_hom f e hi]
  · exact (K.isZero_stupidTrunc_X e j (by simpa using hj)).eq_of_src _ _

/-- The inclusions of stupid truncations form a natural transformation. -/
def stupidTruncInclusionNatTrans :
    e.stupidTruncFunctor C ⟶ Functor.id (HomologicalComplex C c') where
  app K := stupidTruncInclusion K e
  naturality _ _ f := stupidTruncMap_comp_stupidTruncInclusion e f

end HomologicalComplex
