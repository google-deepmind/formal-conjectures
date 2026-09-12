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

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The linear dual of a complex of vector spaces

This file dualises complexes of vector spaces. The reversed algebraic-dual short complex of a
short complex has homology canonically linearly equivalent to the dual of the original homology:
this is the universal-coefficient identification, and no finite-dimensionality hypothesis is
needed.

Applying the dual degreewise turns a nonnegatively graded chain complex into a cochain complex,
whose degree-`n` short complex is the reversed dual of the original one. A chain-homotopy
equivalence therefore induces, contravariantly, a linear equivalence on dual homology.

Duality is contravariantly functorial for maps, isomorphisms, chain homotopies and
chain-homotopy equivalences, so all of these transport to the dual cochain complex.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace CategoryTheory.ShortComplex

variable {R : Type u} [Field R]

/-- The reversed algebraic-dual short complex. -/
def linearDual (S : ShortComplex (ModuleCat.{u} R)) :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk S.g.hom.dualMap S.f.hom.dualMap (by
    ext φ x
    change φ (S.g.hom (S.f.hom x)) = 0
    rw [S.moduleCat_zero_apply, map_zero])

/-- A dual cycle evaluates on a cycle of the original short complex and descends to its
homology. -/
def dualCycleToHomologyFunctional (S : ShortComplex (ModuleCat.{u} R)) :
    LinearMap.ker S.f.hom.dualMap →ₗ[R]
      Module.Dual R S.moduleCatLeftHomologyData.H where
  toFun φ := (LinearMap.range S.moduleCatToCycles).liftQ
    (φ.1.comp (LinearMap.ker S.g.hom).subtype) (by
      rintro _ ⟨x, rfl⟩
      exact LinearMap.congr_fun φ.2 x)
  map_add' φ ψ := by
    ext z
    induction z using Submodule.Quotient.induction_on with
    | _ z => rfl
  map_smul' a φ := by
    ext z
    induction z using Submodule.Quotient.induction_on with
    | _ z => rfl

lemma dualCycleToHomologyFunctional_vanishes_on_boundaries
    (S : ShortComplex (ModuleCat.{u} R)) :
    LinearMap.range (S.linearDual.moduleCatToCycles) ≤
      LinearMap.ker S.dualCycleToHomologyFunctional := by
  rintro _ ⟨ψ, rfl⟩
  change Module.Dual R S.X₃ at ψ
  ext z
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
      change (ψ : Module.Dual R S.X₃) (S.g.hom z.1) = 0
      rw [z.2, map_zero]

/-- The canonical pairing from the explicit homology of the dual complex to the dual of the
explicit homology of the original complex. -/
def dualHomologyComparisonExplicit (S : ShortComplex (ModuleCat.{u} R)) :
    S.linearDual.moduleCatLeftHomologyData.H →ₗ[R]
      Module.Dual R S.moduleCatLeftHomologyData.H :=
  (LinearMap.range S.linearDual.moduleCatToCycles).liftQ
    S.dualCycleToHomologyFunctional
    S.dualCycleToHomologyFunctional_vanishes_on_boundaries

@[simp]
lemma dualHomologyComparisonExplicit_mk_apply_mk
    (S : ShortComplex (ModuleCat.{u} R))
    (φ : LinearMap.ker S.f.hom.dualMap) (z : LinearMap.ker S.g.hom) :
    S.dualHomologyComparisonExplicit (Submodule.Quotient.mk φ)
        (Submodule.Quotient.mk z) = φ.1 z.1 :=
  rfl

lemma dualHomologyComparisonExplicit_surjective
    (S : ShortComplex (ModuleCat.{u} R)) :
    Function.Surjective S.dualHomologyComparisonExplicit := by
  intro α
  change Module.Dual R
    (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) at α
  let αcycles : Module.Dual R (LinearMap.ker S.g.hom) :=
    α.comp (LinearMap.range S.moduleCatToCycles).mkQ
  let φ : Module.Dual R S.X₂ :=
    Subspace.dualLift (LinearMap.ker S.g.hom) αcycles
  have hφ : φ ∈ LinearMap.ker S.f.hom.dualMap := by
    rw [LinearMap.mem_ker]
    ext x
    change φ (S.f.hom x) = 0
    rw [Subspace.dualLift_of_mem (S.moduleCat_zero_apply x)]
    change α (Submodule.Quotient.mk
      (S.moduleCatToCycles x)) = 0
    simpa using congrArg α
      ((Submodule.Quotient.mk_eq_zero _).mpr
        (LinearMap.mem_range_self S.moduleCatToCycles x))
  refine ⟨Submodule.Quotient.mk ⟨φ, hφ⟩, ?_⟩
  ext z
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
      change φ z.1 = α (Submodule.Quotient.mk z)
      rw [Subspace.dualLift_of_subtype]
      rfl

lemma dualHomologyComparisonExplicit_injective
    (S : ShortComplex (ModuleCat.{u} R)) :
    Function.Injective S.dualHomologyComparisonExplicit := by
  intro a b hab
  induction a using Submodule.Quotient.induction_on with
  | _ φ =>
    induction b using Submodule.Quotient.induction_on with
    | _ ψ =>
      change LinearMap.ker S.f.hom.dualMap at φ ψ
      apply (Submodule.Quotient.eq _).mpr
      have hzero : S.dualCycleToHomologyFunctional (φ - ψ) = 0 := by
        change S.dualCycleToHomologyFunctional φ =
          S.dualCycleToHomologyFunctional ψ at hab
        exact (S.dualCycleToHomologyFunctional.map_sub φ ψ).trans
          (sub_eq_zero.mpr hab)
      have hv : (φ - ψ).1 ∈ (LinearMap.ker S.g.hom).dualAnnihilator := by
        rw [Submodule.mem_dualAnnihilator]
        intro z hz
        exact LinearMap.congr_fun hzero (Submodule.Quotient.mk ⟨z, hz⟩)
      rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hv
      obtain ⟨η, hη⟩ := hv
      exact ⟨η, Subtype.ext hη⟩

/-- Universal coefficients for a short complex of vector spaces: the homology of its reversed
dual is canonically linearly equivalent to the dual of its homology. -/
def linearDualHomologyEquiv (S : ShortComplex (ModuleCat.{u} R)) :
    S.linearDual.homology ≃ₗ[R] Module.Dual R S.homology :=
  S.linearDual.moduleCatHomologyIso.toLinearEquiv.trans <|
    (LinearEquiv.ofBijective S.dualHomologyComparisonExplicit
      ⟨S.dualHomologyComparisonExplicit_injective,
        S.dualHomologyComparisonExplicit_surjective⟩).trans <|
      S.moduleCatHomologyIso.toLinearEquiv.dualMap

end CategoryTheory.ShortComplex

namespace HomologicalComplex

variable {R : Type u} [Field R]

/-- The algebraic-dual cochain complex of a nonnegatively graded chain complex of vector
spaces. -/
def linearDualCochainComplex (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of
    (fun n ↦ ModuleCat.of R (Module.Dual R (K.X n)))
    (fun n ↦ ModuleCat.ofHom (K.d (n + 1) n).hom.dualMap)
    (fun n ↦ by
      ext φ c
      change φ ((K.d (n + 1) n).hom ((K.d (n + 2) (n + 1)).hom c)) = 0
      rw [show (K.d (n + 1) n).hom ((K.d (n + 2) (n + 1)).hom c) = 0 from
        ConcreteCategory.congr_hom (K.d_comp_d (n + 2) (n + 1) n) c, map_zero])

@[simp]
lemma linearDualCochainComplex_d (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (K.linearDualCochainComplex).d n (n + 1) =
      ModuleCat.ofHom (K.d (n + 1) n).hom.dualMap := by
  simp [linearDualCochainComplex]

set_option backward.isDefEq.respectTransparency false in
/-- The degree-`n` short complex of a linear-dual cochain complex is the reversed dual of the
degree-`n` short complex of the original chain complex. -/
def linearDualCochainComplexScIso (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    K.linearDualCochainComplex.sc n ≅ (K.sc n).linearDual := by
  let D := K.linearDualCochainComplex
  have hprev : (ComplexShape.up ℕ).prev n = (ComplexShape.down ℕ).next n := by
    cases n <;> simp
  have hnext : (ComplexShape.up ℕ).next n = (ComplexShape.down ℕ).prev n := by simp
  refine D.isoSc' ((ComplexShape.down ℕ).next n) n
      ((ComplexShape.down ℕ).prev n) hprev hnext ≪≫
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id,
      HomologicalComplex.shortComplexFunctor'_obj_f]
    dsimp only [ShortComplex.linearDual, ShortComplex.moduleCatMk, HomologicalComplex.sc,
      HomologicalComplex.shortComplexFunctor, HomologicalComplex.shortComplexFunctor']
    cases n with
    | zero =>
        rw [ChainComplex.next_nat_zero]
        change ModuleCat.ofHom (K.d 0 0).hom.dualMap = D.d 0 0
        rw [K.shape 0 0 (by simp), D.shape 0 0 (by simp)]
        ext φ x
        exact map_zero φ
    | succ n =>
        rw [ChainComplex.next_nat_succ]
        exact (linearDualCochainComplex_d K n).symm
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id,
      HomologicalComplex.shortComplexFunctor'_obj_g]
    dsimp only [ShortComplex.linearDual, ShortComplex.moduleCatMk, HomologicalComplex.sc,
      HomologicalComplex.shortComplexFunctor, HomologicalComplex.shortComplexFunctor']
    rw [ChainComplex.prev]
    exact (linearDualCochainComplex_d K n).symm

variable {K L M : ChainComplex (ModuleCat.{u} R) ℕ}


/-- Algebraic duality sends a map of nonnegative chain complexes contravariantly to a map of
cochain complexes. -/
def linearDualMap (f : K ⟶ L) :
    L.linearDualCochainComplex ⟶ K.linearDualCochainComplex where
  f n := ModuleCat.ofHom (f.f n).hom.dualMap
  comm' i j hij := by
    obtain rfl := hij
    rw [HomologicalComplex.linearDualCochainComplex_d,
      HomologicalComplex.linearDualCochainComplex_d]
    ext φ
    change Module.Dual R (L.X i) at φ
    apply LinearMap.ext
    intro x
    change K.X (i + 1) at x
    change φ ((f.f i).hom ((K.d (i + 1) i).hom x)) =
      φ ((L.d (i + 1) i).hom ((f.f (i + 1)).hom x))
    exact congrArg φ (ConcreteCategory.congr_hom (f.comm (i + 1) i) x).symm

@[simp]
lemma linearDualMap_id (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    linearDualMap (𝟙 K) = 𝟙 K.linearDualCochainComplex :=
  rfl

@[simp]
lemma linearDualMap_comp (f : K ⟶ L) (g : L ⟶ M) :
    linearDualMap (f ≫ g) = linearDualMap g ≫ linearDualMap f :=
  rfl

/-- Algebraic duality sends an isomorphism of chain complexes to an isomorphism of cochain
complexes, reversing its direction. -/
def linearDualIso (e : K ≅ L) :
    L.linearDualCochainComplex ≅ K.linearDualCochainComplex where
  hom := linearDualMap e.hom
  inv := linearDualMap e.inv
  hom_inv_id := by rw [← linearDualMap_comp, e.inv_hom_id, linearDualMap_id]
  inv_hom_id := by rw [← linearDualMap_comp, e.hom_inv_id, linearDualMap_id]

set_option backward.isDefEq.respectTransparency false in
/-- Algebraic duality sends a chain homotopy contravariantly to a cochain homotopy. -/
def linearDualHomotopy {f g : K ⟶ L} (h : Homotopy f g) :
    Homotopy (linearDualMap f) (linearDualMap g) where
  hom i j := ModuleCat.ofHom (h.hom j i).hom.dualMap
  zero i j hij := by
    change ¬(ComplexShape.down ℕ).Rel i j at hij
    rw [h.zero j i hij]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro x
    simp
  comm i := by
    cases i with
    | zero =>
        rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_zero_cochainComplex,
          HomologicalComplex.linearDualCochainComplex_d]
        dsimp only [HomologicalComplex.linearDualCochainComplex] at ⊢
        dsimp only [linearDualMap]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro φ
        change Module.Dual R (L.X 0) at φ
        apply LinearMap.ext
        intro x
        change K.X 0 at x
        have hi := ConcreteCategory.congr_hom (h.comm 0) x
        rw [Homotopy.dNext_zero_chainComplex,
          Homotopy.prevD_chainComplex] at hi
        simp only [ModuleCat.hom_ofHom, ModuleCat.hom_comp, ModuleCat.hom_add,
          ModuleCat.hom_zero, LinearMap.comp_apply, LinearMap.add_apply,
          LinearMap.zero_apply, LinearMap.dualMap_apply] at ⊢
        simpa [add_assoc] using congrArg φ hi
    | succ n =>
        rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_succ_cochainComplex,
          HomologicalComplex.linearDualCochainComplex_d,
          HomologicalComplex.linearDualCochainComplex_d]
        dsimp only [HomologicalComplex.linearDualCochainComplex] at ⊢
        dsimp only [linearDualMap]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro φ
        change Module.Dual R (L.X (n + 1)) at φ
        apply LinearMap.ext
        intro x
        change K.X (n + 1) at x
        have hi := ConcreteCategory.congr_hom (h.comm (n + 1)) x
        rw [Homotopy.dNext_succ_chainComplex,
          Homotopy.prevD_chainComplex] at hi
        simp only [ModuleCat.hom_ofHom, ModuleCat.hom_comp, ModuleCat.hom_add,
          LinearMap.comp_apply, LinearMap.add_apply, LinearMap.dualMap_apply] at ⊢
        simpa [add_assoc, add_comm, add_left_comm] using congrArg φ hi

/-- Algebraic duality sends a chain-homotopy equivalence contravariantly to a cochain-homotopy
equivalence. -/
def linearDualHomotopyEquiv (e : HomotopyEquiv K L) :
    HomotopyEquiv L.linearDualCochainComplex K.linearDualCochainComplex where
  hom := linearDualMap e.hom
  inv := linearDualMap e.inv
  homotopyHomInvId :=
    (Homotopy.ofEq (linearDualMap_comp e.inv e.hom).symm).trans <|
      (linearDualHomotopy e.homotopyInvHomId).trans <|
        Homotopy.ofEq (linearDualMap_id L)
  homotopyInvHomId :=
    (Homotopy.ofEq (linearDualMap_comp e.hom e.inv).symm).trans <|
      (linearDualHomotopy e.homotopyHomInvId).trans <|
        Homotopy.ofEq (linearDualMap_id K)
end HomologicalComplex

namespace HomologicalComplex.HomotopyEquiv

variable {R : Type u} [Field R]
variable {K L : ChainComplex (ModuleCat.{u} R) ℕ}

/-- A chain-homotopy equivalence induces, contravariantly, a linear equivalence on the
cohomology of the algebraic-dual short complexes. -/
def linearDualCohomologyEquiv (h : HomotopyEquiv K L) (n : ℕ) :
    (L.sc n).linearDual.homology ≃ₗ[R] (K.sc n).linearDual.homology :=
  (L.sc n).linearDualHomologyEquiv |>.trans <|
    h.toHomologyIso n |>.toLinearEquiv.dualMap |>.trans <|
      (K.sc n).linearDualHomologyEquiv.symm

end HomologicalComplex.HomotopyEquiv
