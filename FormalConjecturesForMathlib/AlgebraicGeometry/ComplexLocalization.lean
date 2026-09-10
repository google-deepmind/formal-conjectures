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

public import FormalConjecturesForMathlib.AlgebraicGeometry.ComplexAffineScheme
public import Mathlib.Topology.IsLocalHomeomorph

/-!
# Complex points of a localization

Complex algebra homomorphisms from `S[1/f]` are canonically homeomorphic to the open subspace of
complex algebra homomorphisms from `S` at which `f` is nonzero. The forward map is restriction.
Continuity of the extension map follows by representing a localized element as a quotient whose
denominator is a power of `f`.

Nothing here mentions a complex point of a scheme, so it lives in namespace
`AlgebraicGeometry.ComplexAlgHom`: the algebraic model of the complex points of an affine scheme,
as the space of `ℂ`-algebra homomorphisms out of its ring of sections.
-/

@[expose] public section

open scoped Topology

open Topology

namespace AlgebraicGeometry.ComplexAlgHom

open ComplexPoint Point

noncomputable section

variable {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]

/-- Precomposition by a complex algebra equivalence, as an equivalence of complex-valued algebra
homomorphisms. -/
def precompAlgEquiv (e : A ≃ₐ[ℂ] B) : (B →ₐ[ℂ] ℂ) ≃ (A →ₐ[ℂ] ℂ) :=
  AlgEquiv.arrowCongr e.symm (AlgEquiv.refl : ℂ ≃ₐ[ℂ] ℂ)

lemma continuous_precompAlgEquiv (e : A ≃ₐ[ℂ] B) :
    Continuous (precompAlgEquiv e) := by
  rw [continuous_induced_rng]
  exact continuous_pi fun a ↦ continuous_affineAlgebraHom_apply B (e a)

lemma continuous_precompAlgEquiv_symm (e : A ≃ₐ[ℂ] B) :
    Continuous (precompAlgEquiv e).symm := by
  rw [continuous_induced_rng]
  exact continuous_pi fun b ↦ continuous_affineAlgebraHom_apply A (e.symm b)

/-- Precomposition by a complex algebra equivalence is a homeomorphism for pointwise
convergence. -/
def precompAlgEquivHomeomorph (e : A ≃ₐ[ℂ] B) :
    (B →ₐ[ℂ] ℂ) ≃ₜ (A →ₐ[ℂ] ℂ) where
  toEquiv := precompAlgEquiv e
  continuous_toFun := continuous_precompAlgEquiv e
  continuous_invFun := continuous_precompAlgEquiv_symm e

variable (S : Type) [CommRing S] [Algebra ℂ S]

/-- The open subspace of complex algebra homomorphisms at which `f` does not vanish. -/
abbrev nonvanishingAlgHom (f : S) := {u : S →ₐ[ℂ] ℂ // u f ≠ 0}

/-- Restriction of an algebra homomorphism from `S[1/f]` to `S`, bundled with its nonvanishing
property. -/
def localizationAwayAlgHomRestriction (f : S) (u : Localization.Away f →ₐ[ℂ] ℂ) :
    nonvanishingAlgHom S f :=
  ⟨u.comp (IsScalarTower.toAlgHom ℂ S (Localization.Away f)),
    ((IsLocalization.Away.algebraMap_isUnit f).map u).ne_zero⟩

/-- Extension of an algebra homomorphism on which `f` is nonzero to `S[1/f]`. -/
def nonvanishingAlgHomExtension (f : S) (u : nonvanishingAlgHom S f) :
    Localization.Away f →ₐ[ℂ] ℂ :=
  IsLocalization.Away.liftAlgHom f (isUnit_iff_ne_zero.mpr u.2)

@[simp]
lemma nonvanishingAlgHomExtension_algebraMap (f : S) (u : nonvanishingAlgHom S f) (s : S) :
    nonvanishingAlgHomExtension S f u (algebraMap S (Localization.Away f) s) = u.1 s := by
  change IsLocalization.Away.lift f (isUnit_iff_ne_zero.mpr u.2)
    (algebraMap S (Localization.Away f) s) = u.1 s
  exact IsLocalization.Away.lift_eq f (isUnit_iff_ne_zero.mpr u.2) s

@[simp]
lemma localizationAwayAlgHomRestriction_apply (f : S)
    (u : Localization.Away f →ₐ[ℂ] ℂ) (s : S) :
    (localizationAwayAlgHomRestriction S f u).1 s =
      u (algebraMap S (Localization.Away f) s) :=
  rfl

/-- The algebraic equivalence between homomorphisms from `S[1/f]` and homomorphisms from `S` on
which `f` does not vanish. -/
def localizationAwayAlgHomEquiv (f : S) :
    (Localization.Away f →ₐ[ℂ] ℂ) ≃ nonvanishingAlgHom S f where
  toFun := localizationAwayAlgHomRestriction S f
  invFun := nonvanishingAlgHomExtension S f
  left_inv u := by
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (.powers f)
    refine DFunLike.ext _ _ fun s ↦ ?_
    change nonvanishingAlgHomExtension S f (localizationAwayAlgHomRestriction S f u)
      (algebraMap S (Localization.Away f) s) = u (algebraMap S (Localization.Away f) s)
    rw [nonvanishingAlgHomExtension_algebraMap, localizationAwayAlgHomRestriction_apply]
  right_inv u := by
    apply Subtype.ext
    exact AlgHom.coe_ringHom_injective
      (DFunLike.ext _ _ (nonvanishingAlgHomExtension_algebraMap S f u))

lemma continuous_localizationAwayAlgHomEquiv (f : S) :
    Continuous (localizationAwayAlgHomEquiv S f) := by
  apply Continuous.subtype_mk
  rw [continuous_induced_rng]
  exact continuous_pi fun s ↦
    continuous_affineAlgebraHom_apply (Localization.Away f) (algebraMap S _ s)

lemma localizationAwayAlgHomEquiv_symm_apply_eq_div (f : S)
    (x : Localization.Away f) :
    ∃ (n : ℕ) (a : S), ∀ u : nonvanishingAlgHom S f,
      (localizationAwayAlgHomEquiv S f).symm u x = u.1 a / u.1 f ^ n := by
  obtain ⟨n, a, hxa⟩ := IsLocalization.Away.surj f x
  refine ⟨n, a, fun u ↦ ?_⟩
  have h := congrArg (nonvanishingAlgHomExtension S f u) hxa
  change nonvanishingAlgHomExtension S f u x = u.1 a / u.1 f ^ n
  apply (eq_div_iff (pow_ne_zero n u.2)).2
  simpa only [map_mul, map_pow, nonvanishingAlgHomExtension_algebraMap] using h

lemma continuous_localizationAwayAlgHomEquiv_symm (f : S) :
    Continuous (localizationAwayAlgHomEquiv S f).symm := by
  rw [continuous_induced_rng]
  refine continuous_pi fun x ↦ ?_
  obtain ⟨n, a, h⟩ := localizationAwayAlgHomEquiv_symm_apply_eq_div S f x
  have ha : Continuous (fun u : nonvanishingAlgHom S f ↦ u.1 a) :=
    (continuous_affineAlgebraHom_apply S a).comp continuous_subtype_val
  have hf : Continuous (fun u : nonvanishingAlgHom S f ↦ u.1 f) :=
    (continuous_affineAlgebraHom_apply S f).comp continuous_subtype_val
  exact (ha.div (hf.pow n) fun u ↦ pow_ne_zero n u.2).congr fun u ↦ (h u).symm

/-- Complex points of `S[1/f]` are homeomorphic to the nonvanishing locus of `f` in the complex
points of `S`. -/
def localizationAwayAlgHomHomeomorph (f : S) :
    (Localization.Away f →ₐ[ℂ] ℂ) ≃ₜ nonvanishingAlgHom S f where
  toEquiv := localizationAwayAlgHomEquiv S f
  continuous_toFun := continuous_localizationAwayAlgHomEquiv S f
  continuous_invFun := continuous_localizationAwayAlgHomEquiv_symm S f

/-- Restriction from complex points of `S[1/f]` to complex points of `S`, with the nonvanishing
witness forgotten. -/
def localizationAwayAlgHomMap (f : S) :
    (Localization.Away f →ₐ[ℂ] ℂ) → (S →ₐ[ℂ] ℂ) :=
  fun u ↦ (localizationAwayAlgHomRestriction S f u).1

lemma isOpen_nonvanishingAlgHom (f : S) :
    IsOpen {u : S →ₐ[ℂ] ℂ | u f ≠ 0} :=
  isOpen_ne_fun (continuous_affineAlgebraHom_apply S f) continuous_const

/-- Restriction from `S[1/f]` identifies its complex points with an open subspace of the complex
points of `S`. -/
lemma isOpenEmbedding_localizationAwayAlgHomMap (f : S) :
    IsOpenEmbedding (localizationAwayAlgHomMap S f) :=
  (isOpen_nonvanishingAlgHom S f).isOpenEmbedding_subtypeVal.comp
    (localizationAwayAlgHomHomeomorph S f).isOpenEmbedding

lemma isLocalHomeomorph_localizationAwayAlgHomMap (f : S) :
    IsLocalHomeomorph (localizationAwayAlgHomMap S f) :=
  (isOpenEmbedding_localizationAwayAlgHomMap S f).isLocalHomeomorph

end


end AlgebraicGeometry.ComplexAlgHom
