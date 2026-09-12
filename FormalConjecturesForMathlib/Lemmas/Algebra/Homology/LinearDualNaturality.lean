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

public import FormalConjecturesForMathlib.Definitions.AlgebraicTopology.SingularCochainCohomology

/-!
# Naturality of linear duality on homology

Concrete cycle representatives and the canonical universal-coefficient equivalence are
compatible with actual morphisms of short complexes. These identities are used to descend
geometric cap-product identities in the cohomology variable.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory.ShortComplex

variable {R : Type u} [Field R]

/-- The canonical class of an explicit cycle in a short complex of vector spaces. -/
def moduleCatHomologyClass (S : ShortComplex (ModuleCat.{u} R)) :
    LinearMap.ker S.g.hom →ₗ[R] S.homology :=
  S.moduleCatHomologyIso.inv.hom.comp (LinearMap.range S.moduleCatToCycles).mkQ

/-- Every homology class has an explicit cycle representative. -/
lemma moduleCatHomologyClass_surjective (S : ShortComplex (ModuleCat.{u} R)) :
    Function.Surjective S.moduleCatHomologyClass :=
  S.moduleCatHomologyIso.toLinearEquiv.symm.surjective.comp
    (Submodule.mkQ_surjective _)

set_option backward.isDefEq.respectTransparency false in
/-- A morphism of short complexes sends cycles to cycles. -/
def moduleCatCycleMap {S T : ShortComplex (ModuleCat.{u} R)} (f : S ⟶ T) :
    LinearMap.ker S.g.hom →ₗ[R] LinearMap.ker T.g.hom :=
  f.τ₂.hom.restrict (fun x hx ↦ by
    change T.g.hom (f.τ₂.hom x) = 0
    have h := ConcreteCategory.congr_hom f.comm₂₃ x
    change T.g.hom (f.τ₂.hom x) = f.τ₃.hom (S.g.hom x) at h
    rwa [show S.g.hom x = 0 from hx, map_zero] at h)

set_option backward.isDefEq.respectTransparency false in
lemma moduleCatCyclesIso_inv_cycleMap {S T : ShortComplex (ModuleCat.{u} R)}
    (f : S ⟶ T) :
    S.moduleCatCyclesIso.inv ≫ cyclesMap f =
      ModuleCat.ofHom (moduleCatCycleMap f) ≫ T.moduleCatCyclesIso.inv := by
  rw [← cancel_mono T.iCycles]
  simp only [Category.assoc, cyclesMap_i, moduleCatCyclesIso_inv_iCycles_assoc,
    moduleCatCyclesIso_inv_iCycles]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Taking the class of a cycle commutes with the induced homology map. -/
lemma moduleCatHomologyClass_naturality {S T : ShortComplex (ModuleCat.{u} R)}
    (f : S ⟶ T) (x : LinearMap.ker S.g.hom) :
    (homologyMap f).hom (S.moduleCatHomologyClass x) =
      T.moduleCatHomologyClass (moduleCatCycleMap f x) := by
  have h :
      S.moduleCatCyclesIso.inv ≫ S.homologyπ ≫ homologyMap f =
        ModuleCat.ofHom (moduleCatCycleMap f) ≫ T.moduleCatCyclesIso.inv ≫ T.homologyπ := by
    rw [homologyπ_naturality, ← Category.assoc, moduleCatCyclesIso_inv_cycleMap,
      Category.assoc]
  rw [← Category.assoc, moduleCatCyclesIso_inv_π,
    moduleCatCyclesIso_inv_π] at h
  exact ConcreteCategory.congr_hom h x

set_option backward.isDefEq.respectTransparency false in
/-- Reversed linear-dual short complexes are contravariantly functorial. -/
def linearDualMap {S T : ShortComplex (ModuleCat.{u} R)} (f : S ⟶ T) :
    T.linearDual ⟶ S.linearDual where
  τ₁ := ModuleCat.ofHom f.τ₃.hom.dualMap
  τ₂ := ModuleCat.ofHom f.τ₂.hom.dualMap
  τ₃ := ModuleCat.ofHom f.τ₁.hom.dualMap
  comm₁₂ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro phi
    change Module.Dual R T.X₃ at phi
    apply LinearMap.ext
    intro x
    exact congrArg phi (ConcreteCategory.congr_hom f.comm₂₃ x).symm
  comm₂₃ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro phi
    change Module.Dual R T.X₂ at phi
    apply LinearMap.ext
    intro x
    exact congrArg phi (ConcreteCategory.congr_hom f.comm₁₂ x).symm

set_option backward.isDefEq.respectTransparency false in
/-- Universal coefficients evaluate a dual cycle on an ordinary cycle without any
choice of generators or representatives in the resulting pairing. -/
lemma linearDualHomologyEquiv_class_apply_class (S : ShortComplex (ModuleCat.{u} R))
    (phi : LinearMap.ker S.f.hom.dualMap) (x : LinearMap.ker S.g.hom) :
    S.linearDualHomologyEquiv (S.linearDual.moduleCatHomologyClass phi)
        (S.moduleCatHomologyClass x) = (phi.1 : Module.Dual R S.X₂) x.1 := by
  change S.dualHomologyComparisonExplicit
      (S.linearDual.moduleCatHomologyIso.hom.hom
        (S.linearDual.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk phi)))
      (S.moduleCatHomologyIso.hom.hom
        (S.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk x))) =
      (phi.1 : Module.Dual R S.X₂) x.1
  have hphi := ConcreteCategory.congr_hom
    S.linearDual.moduleCatHomologyIso.inv_hom_id (Submodule.Quotient.mk phi)
  have hx := ConcreteCategory.congr_hom
    S.moduleCatHomologyIso.inv_hom_id (Submodule.Quotient.mk x)
  change S.linearDual.moduleCatHomologyIso.hom.hom
    (S.linearDual.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk phi)) =
      Submodule.Quotient.mk phi at hphi
  change S.moduleCatHomologyIso.hom.hom
    (S.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk x)) =
      Submodule.Quotient.mk x at hx
  rw [hphi, hx]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The constructed universal-coefficient equivalence is natural, not merely an
abstract isomorphism between vector spaces of the same dimension. -/
theorem linearDualHomologyEquiv_naturality
    {S T : ShortComplex (ModuleCat.{u} R)} (f : S ⟶ T)
    (alpha : T.linearDual.homology) :
    S.linearDualHomologyEquiv ((homologyMap (linearDualMap f)).hom alpha) =
      (homologyMap f).hom.dualMap (T.linearDualHomologyEquiv alpha) := by
  obtain ⟨phi, rfl⟩ := T.linearDual.moduleCatHomologyClass_surjective alpha
  apply LinearMap.ext
  intro c
  obtain ⟨x, rfl⟩ := S.moduleCatHomologyClass_surjective c
  change S.linearDualHomologyEquiv
      ((homologyMap (linearDualMap f)).hom (T.linearDual.moduleCatHomologyClass phi))
      (S.moduleCatHomologyClass x) =
    T.linearDualHomologyEquiv (T.linearDual.moduleCatHomologyClass phi)
      ((homologyMap f).hom (S.moduleCatHomologyClass x))
  rw [moduleCatHomologyClass_naturality, moduleCatHomologyClass_naturality,
    linearDualHomologyEquiv_class_apply_class, linearDualHomologyEquiv_class_apply_class]
  rfl

end CategoryTheory.ShortComplex
