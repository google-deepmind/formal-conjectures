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

public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Quotient.Basic

import Mathlib.Algebra.Algebra.NonUnitalHom

/-!
# Algebraic de Rham forms

This file gives an explicit generators-and-relations construction of relative Kähler differential
forms. Degree `p` is generated over the base ring by symbols
`a₀ da₁ ∧ ... ∧ daₚ`. The relations impose linearity, the Leibniz rule, vanishing on base
constants, and alternation. We take their differential closure so that inserting the coefficient
as the first differential defines the exterior derivative by construction.

Algebra homomorphisms act on every entry of a symbol. The resulting maps commute with the exterior
derivative, are functorial, and require no chosen bases or presentations of the algebra.
-/

@[expose] public noncomputable section

open Finsupp

universe u

namespace Algebra.DeRham

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- A symbol `a₀ da₁ ∧ ... ∧ daₚ`. -/
abbrev Generator (p : ℕ) := A × (Fin p → A)

/-- The free module on differential-form symbols. -/
abbrev RawForm (p : ℕ) := Generator A p →₀ R

inductive Relation (p : ℕ)
  | coeffAdd (a b : A) (v : Fin p → A)
  | coeffSMul (r : R) (a : A) (v : Fin p → A)
  | diffAdd (a₀ : A) (v : Fin p → A) (i : Fin p) (a b : A)
  | diffSMul (a₀ : A) (v : Fin p → A) (i : Fin p) (r : R) (a : A)
  | diffMul (a₀ : A) (v : Fin p → A) (i : Fin p) (a b : A)
  | diffConst (a₀ : A) (v : Fin p → A) (i : Fin p) (r : R)
  | alt (a₀ : A) (v : Fin p → A) (i j : Fin p) (h : v i = v j) (hne : i ≠ j)

def relationValue (p : ℕ) : Relation R A p → RawForm R A p
  | .coeffAdd a b v =>
      single (a + b, v) 1 - single (a, v) 1 - single (b, v) 1
  | .coeffSMul r a v =>
      single (r • a, v) 1 - r • single (a, v) 1
  | .diffAdd a₀ v i a b =>
      single (a₀, Function.update v i (a + b)) 1 -
        single (a₀, Function.update v i a) 1 -
          single (a₀, Function.update v i b) 1
  | .diffSMul a₀ v i r a =>
      single (a₀, Function.update v i (r • a)) 1 -
        r • single (a₀, Function.update v i a) 1
  | .diffMul a₀ v i a b =>
      single (a₀, Function.update v i (a * b)) 1 -
        single (a₀ * a, Function.update v i b) 1 -
          single (a₀ * b, Function.update v i a) 1
  | .diffConst a₀ v i r =>
      single (a₀, Function.update v i (algebraMap R A r)) 1
  | .alt a₀ v _ _ _ _ => single (a₀, v) 1

def standardRelations (p : ℕ) : Submodule R (RawForm R A p) :=
  Submodule.span R (Set.range (relationValue R A p))

def nextGenerator {p : ℕ} (g : Generator A p) : Generator A (p + 1) :=
  (1, Fin.cases g.1 g.2)

def rawDifferential (p : ℕ) : RawForm R A p →ₗ[R] RawForm R A (p + 1) :=
  Finsupp.lsum R fun g => Finsupp.lsingle (nextGenerator A g)

omit [Algebra R A] in
@[simp] lemma rawDifferential_single (p : ℕ) (g : Generator A p) (r : R) :
    rawDifferential R A p (single g r) = single (nextGenerator A g) r := by
  simp [rawDifferential]

lemma rawDifferential_squared_single_mem_standardRelations (p : ℕ)
    (g : Generator A p) (r : R) :
    rawDifferential R A (p + 1) (rawDifferential R A p (single g r)) ∈
      standardRelations R A (p + 2) := by
  rw [rawDifferential_single, rawDifferential_single]
  let w : Fin (p + 2) → A := Fin.cases 0 (Fin.cases g.1 g.2)
  have hrel : relationValue R A (p + 2) (Relation.diffConst 1 w 0 1) ∈
      standardRelations R A (p + 2) :=
    Submodule.subset_span (Set.mem_range_self _)
  convert (standardRelations R A (p + 2)).smul_mem r hrel using 1
  simp only [relationValue, smul_single, smul_eq_mul, mul_one]
  congr 2
  apply Prod.ext
  · rfl
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [nextGenerator, w]

lemma rawDifferential_squared_mem_standardRelations (p : ℕ) (x : RawForm R A p) :
    rawDifferential R A (p + 1) (rawDifferential R A p x) ∈
      standardRelations R A (p + 2) := by
  classical
  induction x using Finsupp.induction with
  | zero => simp
  | single_add g r x hg hr ih =>
      rw [map_add, map_add]
      exact Submodule.add_mem _
        (rawDifferential_squared_single_mem_standardRelations R A p g r) ih

/-- The differential closure of the standard relations on form symbols. -/
def relations : (p : ℕ) → Submodule R (RawForm R A p)
  | 0 => standardRelations R A 0
  | p + 1 => standardRelations R A (p + 1) ⊔
      (relations p).map (rawDifferential R A p)

lemma standardRelations_le_relations (p : ℕ) :
    standardRelations R A p ≤ relations R A p := by
  cases p with
  | zero => exact le_rfl
  | succ p => exact le_sup_left

lemma rawDifferential_mem_relations (p : ℕ) {x : RawForm R A p}
    (hx : x ∈ relations R A p) :
    rawDifferential R A p x ∈ relations R A (p + 1) := by
  apply (le_sup_right :
    (relations R A p).map (rawDifferential R A p) ≤ relations R A (p + 1))
  exact ⟨x, hx, rfl⟩

/-- Relative Kähler differential forms in degree `p`, by generators and relations. -/
abbrev Form (p : ℕ) := RawForm R A p ⧸ relations R A p

def mk (p : ℕ) (a₀ : A) (v : Fin p → A) : Form R A p :=
  Submodule.Quotient.mk (single (a₀, v) 1)

lemma relationValue_eq_zero (p : ℕ) (r : Relation R A p) :
    Submodule.Quotient.mk (relationValue R A p r) = (0 : Form R A p) := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact standardRelations_le_relations R A p
    (Submodule.subset_span (Set.mem_range_self r))

@[simp] lemma mk_coeff_add (p : ℕ) (a b : A) (v : Fin p → A) :
    mk R A p (a + b) v = mk R A p a v + mk R A p b v := by
  have h := relationValue_eq_zero R A p (Relation.coeffAdd a b v)
  exact eq_add_of_sub_eq' (by simpa [relationValue, mk, sub_eq_zero] using h)

@[simp] lemma mk_coeff_smul (p : ℕ) (r : R) (a : A) (v : Fin p → A) :
    mk R A p (r • a) v = r • mk R A p a v := by
  have h := relationValue_eq_zero R A p (Relation.coeffSMul r a v)
  calc
    _ = Submodule.Quotient.mk (single (a, v) r) := by
      simpa [relationValue, mk, sub_eq_zero] using h
    _ = r • mk R A p a v := by
      change Submodule.Quotient.mk (single (a, v) r) =
        r • Submodule.Quotient.mk (single (a, v) 1)
      rw [← Submodule.Quotient.mk_smul (relations R A p)]
      simp

/-- A function regarded as a differential form of degree zero. -/
def ofFunction : A →ₗ[R] Form R A 0 where
  toFun a := mk R A 0 a Fin.elim0
  map_add' a b := mk_coeff_add R A 0 a b Fin.elim0
  map_smul' r a := mk_coeff_smul R A 0 r a Fin.elim0

@[simp] lemma ofFunction_apply (a : A) :
    ofFunction R A a = mk R A 0 a Fin.elim0 := rfl

/-- A scalar from the base ring regarded as a differential form of degree zero. -/
def ofConstant : R →ₗ[R] Form R A 0 :=
  (ofFunction R A).comp (Algebra.linearMap R A)

@[simp] lemma ofConstant_apply (r : R) :
    ofConstant R A r = ofFunction R A (algebraMap R A r) := rfl

@[simp] lemma mk_diff_add (p : ℕ) (a₀ : A) (v : Fin p → A) (i : Fin p) (a b : A) :
    mk R A p a₀ (Function.update v i (a + b)) =
      mk R A p a₀ (Function.update v i a) +
        mk R A p a₀ (Function.update v i b) := by
  have h := relationValue_eq_zero R A p (Relation.diffAdd a₀ v i a b)
  exact eq_add_of_sub_eq' (by simpa [relationValue, mk, sub_eq_zero] using h)

@[simp] lemma mk_diff_smul (p : ℕ) (a₀ : A) (v : Fin p → A) (i : Fin p)
    (r : R) (a : A) :
    mk R A p a₀ (Function.update v i (r • a)) =
      r • mk R A p a₀ (Function.update v i a) := by
  have h := relationValue_eq_zero R A p (Relation.diffSMul a₀ v i r a)
  calc
    _ = Submodule.Quotient.mk (single (a₀, Function.update v i a) r) := by
      simpa [relationValue, mk, sub_eq_zero] using h
    _ = r • mk R A p a₀ (Function.update v i a) := by
      change Submodule.Quotient.mk (single (a₀, Function.update v i a) r) =
        r • Submodule.Quotient.mk (single (a₀, Function.update v i a) 1)
      rw [← Submodule.Quotient.mk_smul (relations R A p)]
      simp

@[simp] lemma mk_diff_mul (p : ℕ) (a₀ : A) (v : Fin p → A) (i : Fin p) (a b : A) :
    mk R A p a₀ (Function.update v i (a * b)) =
      mk R A p (a₀ * a) (Function.update v i b) +
        mk R A p (a₀ * b) (Function.update v i a) := by
  have h := relationValue_eq_zero R A p (Relation.diffMul a₀ v i a b)
  exact eq_add_of_sub_eq' (by simpa [relationValue, mk, sub_eq_zero] using h)

@[simp] lemma mk_diff_const (p : ℕ) (a₀ : A) (v : Fin p → A) (i : Fin p) (r : R) :
    mk R A p a₀ (Function.update v i (algebraMap R A r)) = 0 :=
  relationValue_eq_zero R A p (Relation.diffConst a₀ v i r)

@[simp] lemma mk_alt (p : ℕ) (a₀ : A) (v : Fin p → A) (i j : Fin p)
    (h : v i = v j) (hne : i ≠ j) :
    mk R A p a₀ v = 0 :=
  relationValue_eq_zero R A p (Relation.alt a₀ v i j h hne)

/-- The exterior derivative on the generators-and-relations model of differential forms. -/
def differential (p : ℕ) : Form R A p →ₗ[R] Form R A (p + 1) :=
  (relations R A p).liftQ
    ((relations R A (p + 1)).mkQ.comp (rawDifferential R A p)) <| by
      intro x hx
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact rawDifferential_mem_relations R A p hx

@[simp] lemma differential_mk (p : ℕ) (a₀ : A) (v : Fin p → A) :
    differential R A p (mk R A p a₀ v) =
      mk R A (p + 1) 1 (Fin.cases a₀ v) := by
  simp [differential, mk, rawDifferential_single, nextGenerator]

@[simp] lemma differential_ofFunction_algebraMap (r : R) :
    differential R A 0 (ofFunction R A (algebraMap R A r)) = 0 := by
  rw [ofFunction_apply, differential_mk, show Fin.cases (algebraMap R A r) Fin.elim0 =
      Function.update (fun _ : Fin 1 => (0 : A)) 0 (algebraMap R A r) by
    funext i
    obtain rfl := Fin.eq_zero i
    simp]
  exact mk_diff_const R A 1 1 (fun _ => 0) 0 r

@[simp] lemma differential_ofConstant (r : R) :
    differential R A 0 (ofConstant R A r) = 0 := by
  rw [ofConstant_apply, differential_ofFunction_algebraMap]

lemma differential_squared (p : ℕ) (x : Form R A p) :
    differential R A (p + 1) (differential R A p x) = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (relations R A p) x
  change Submodule.Quotient.mk
    (rawDifferential R A (p + 1) (rawDifferential R A p x)) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact standardRelations_le_relations R A (p + 2)
    (rawDifferential_squared_mem_standardRelations R A p x)

variable {A} {B : Type u} [CommRing B] [Algebra R B]

/-- Apply an algebra homomorphism to every coefficient in a form symbol. -/
def generatorMap (f : A →ₐ[R] B) (p : ℕ) : Generator A p → Generator B p :=
  fun g => (f g.1, fun i => f (g.2 i))

/-- The map on free form symbols induced by an algebra homomorphism. -/
def rawMap (f : A →ₐ[R] B) (p : ℕ) : RawForm R A p →ₗ[R] RawForm R B p :=
  Finsupp.lmapDomain R R (generatorMap R f p)

@[simp] lemma rawMap_single (f : A →ₐ[R] B) (p : ℕ) (g : Generator A p) (r : R) :
    rawMap R f p (single g r) = single (generatorMap R f p g) r := by
  simp [rawMap]

lemma generatorMap_update (f : A →ₐ[R] B) (p : ℕ) (a₀ : A)
    (v : Fin p → A) (i : Fin p) (a : A) :
    generatorMap R f p (a₀, Function.update v i a) =
      (f a₀, Function.update (fun j => f (v j)) i (f a)) := by
  apply Prod.ext
  · rfl
  · funext j
    by_cases h : j = i <;> simp [generatorMap, h]

lemma rawMap_relationValue_mem_standardRelations (f : A →ₐ[R] B) (p : ℕ)
    (r : Relation R A p) :
    rawMap R f p (relationValue R A p r) ∈ standardRelations R B p := by
  apply Submodule.subset_span
  cases r with
  | coeffAdd a b v =>
      refine ⟨Relation.coeffAdd (f a) (f b) (fun i => f (v i)), ?_⟩
      simp [relationValue, generatorMap]
  | coeffSMul r a v =>
      refine ⟨Relation.coeffSMul r (f a) (fun i => f (v i)), ?_⟩
      simp [relationValue, generatorMap]
  | diffAdd a₀ v i a b =>
      refine ⟨Relation.diffAdd (f a₀) (fun j => f (v j)) i (f a) (f b), ?_⟩
      simp [relationValue, generatorMap_update R]
  | diffSMul a₀ v i r a =>
      refine ⟨Relation.diffSMul (f a₀) (fun j => f (v j)) i r (f a), ?_⟩
      simp [relationValue, generatorMap_update R]
  | diffMul a₀ v i a b =>
      refine ⟨Relation.diffMul (f a₀) (fun j => f (v j)) i (f a) (f b), ?_⟩
      simp [relationValue, generatorMap_update R]
  | diffConst a₀ v i r =>
      refine ⟨Relation.diffConst (f a₀) (fun j => f (v j)) i r, ?_⟩
      simp [relationValue, generatorMap_update R]
  | alt a₀ v i j h hne =>
      refine ⟨Relation.alt (f a₀) (fun k => f (v k)) i j (congrArg f h) hne, ?_⟩
      simp [relationValue, generatorMap]

lemma rawMap_standardRelations (f : A →ₐ[R] B) (p : ℕ) {x : RawForm R A p}
    (hx : x ∈ standardRelations R A p) :
    rawMap R f p x ∈ standardRelations R B p := by
  refine Submodule.span_induction (p := fun y _ =>
      rawMap R f p y ∈ standardRelations R B p)
    (fun _ hr => by
      obtain ⟨r, rfl⟩ := hr
      exact rawMap_relationValue_mem_standardRelations R f p r)
    (by simp)
    (fun _ _ _ _ hx hy => by simpa using Submodule.add_mem _ hx hy)
    (fun r _ _ hx => by simpa using (standardRelations R B p).smul_mem r hx)
    hx

lemma rawMap_rawDifferential (f : A →ₐ[R] B) (p : ℕ) (x : RawForm R A p) :
    rawMap R f (p + 1) (rawDifferential R A p x) =
      rawDifferential R B p (rawMap R f p x) := by
  classical
  induction x using Finsupp.induction with
  | zero => simp
  | single_add g r x hg hr ih =>
      simp only [map_add, rawDifferential_single, rawMap_single]
      rw [ih]
      congr 2
      apply Prod.ext
      · simp [generatorMap, nextGenerator]
      · funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp [generatorMap, nextGenerator]

@[simp] lemma rawMap_id (p : ℕ) :
    rawMap R (AlgHom.id R A) p = LinearMap.id := by
  apply LinearMap.ext
  intro x
  classical
  induction x using Finsupp.induction with
  | zero => simp
  | single_add g r x hg hr ih =>
      simp only [map_add, rawMap_single, generatorMap, AlgHom.id_apply,
        LinearMap.id_coe, id_eq]
      rw [ih]
      congr 2

variable {C : Type u} [CommRing C] [Algebra R C]

@[simp] lemma rawMap_comp (f : A →ₐ[R] B) (g : B →ₐ[R] C) (p : ℕ) :
    rawMap R (g.comp f) p = (rawMap R g p).comp (rawMap R f p) := by
  apply LinearMap.ext
  intro x
  classical
  induction x using Finsupp.induction with
  | zero => simp
  | single_add a r x ha hr ih =>
      simp only [map_add, rawMap_single, generatorMap, AlgHom.coe_comp,
        Function.comp_apply, LinearMap.comp_apply]
      rw [ih]
      rfl

lemma rawMap_relations (f : A →ₐ[R] B) (p : ℕ) {x : RawForm R A p}
    (hx : x ∈ relations R A p) :
    rawMap R f p x ∈ relations R B p := by
  induction p with
  | zero =>
      exact rawMap_standardRelations R f 0 hx
  | succ p ih =>
      rw [relations] at hx
      rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, ⟨w, hw, rfl⟩, rfl⟩
      rw [map_add, rawMap_rawDifferential R]
      apply Submodule.add_mem
      · exact standardRelations_le_relations R B (p + 1)
          (rawMap_standardRelations R f (p + 1) hy)
      · exact rawDifferential_mem_relations R B p (ih hw)

/-- Pull differential forms forward along an algebra homomorphism. -/
def map (f : A →ₐ[R] B) (p : ℕ) : Form R A p →ₗ[R] Form R B p :=
  (relations R A p).liftQ ((relations R B p).mkQ.comp (rawMap R f p)) <| by
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact rawMap_relations R f p hx

@[simp] lemma map_mk (f : A →ₐ[R] B) (p : ℕ) (a₀ : A) (v : Fin p → A) :
    map R f p (mk R A p a₀ v) = mk R B p (f a₀) (fun i => f (v i)) := by
  simp [map, mk, rawMap, generatorMap]

@[simp] lemma map_ofFunction (f : A →ₐ[R] B) (a : A) :
    map R f 0 (ofFunction R A a) = ofFunction R B (f a) := by
  rw [ofFunction_apply, map_mk, ofFunction_apply]
  exact congrArg _ (funext fun i : Fin 0 => i.elim0)

@[simp] lemma map_ofConstant (f : A →ₐ[R] B) (r : R) :
    map R f 0 (ofConstant R A r) = ofConstant R B r := by
  rw [ofConstant_apply, map_ofFunction, f.commutes, ofConstant_apply]

lemma map_differential (f : A →ₐ[R] B) (p : ℕ) (x : Form R A p) :
    map R f (p + 1) (differential R A p x) =
      differential R B p (map R f p x) := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (relations R A p) x
  change Submodule.Quotient.mk (rawMap R f (p + 1) (rawDifferential R A p x)) =
    Submodule.Quotient.mk (rawDifferential R B p (rawMap R f p x))
  rw [rawMap_rawDifferential R]

@[simp] lemma map_id (p : ℕ) : map R (AlgHom.id R A) p = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (relations R A p) x
  apply (Submodule.Quotient.eq (relations R A p)).2
  have hraw : rawMap R (AlgHom.id R A) p x = x := by
    classical
    induction x using Finsupp.induction with
    | zero => simp
    | single_add g r x hg hr ih =>
        simp only [map_add, rawMap_single, generatorMap, AlgHom.id_apply]
        rw [ih]
  rw [hraw, sub_self]
  exact Submodule.zero_mem _

@[simp] lemma map_comp (f : A →ₐ[R] B) (g : B →ₐ[R] C) (p : ℕ) :
    map R (g.comp f) p = (map R g p).comp (map R f p) := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (relations R A p) x
  apply (Submodule.Quotient.eq (relations R C p)).2
  have hraw : rawMap R (g.comp f) p x = rawMap R g p (rawMap R f p x) := by
    classical
    induction x using Finsupp.induction with
    | zero => simp
    | single_add a r x ha hr ih =>
        simp only [map_add, rawMap_single, generatorMap, AlgHom.coe_comp,
          Function.comp_apply]
        rw [ih]
  rw [hraw, sub_self]
  exact Submodule.zero_mem _

end Algebra.DeRham
