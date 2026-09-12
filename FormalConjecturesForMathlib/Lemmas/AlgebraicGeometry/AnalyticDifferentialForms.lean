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

public import FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.AnalyticDifferentialForms

/-!
# Analytic differential forms

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.AnalyticDifferentialForms`.
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialForm TopologicalSpace
open scoped ContDiff Manifold

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ)) (d : ℕ)

attribute [local instance] chartFieldModule

attribute [local instance] chartFieldTower

lemma chartEvaluation_apply_of_notMem [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (z : ComplexPoint X) (p : ℕ)
    (θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p)
    {y : Fin d → ℂ} (hy : y ∉ chartSectionDomain X d U z) :
    chartEvaluation X d U z p θ y = 0 :=
  extendByZero_apply_of_notMem X d U z _ hy

lemma chartEvaluationKernel_eq_top_of_lt [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    {p : ℕ} (hp : d < p) : chartEvaluationKernel X d U p = ⊤ := by
  refine top_unique fun θ _ ↦ ?_
  refine (mem_chartEvaluationKernel_iff X d U p θ).2 fun z y hy ↦
    ContinuousAlternatingMap.ext fun v ↦ ?_
  refine (chartEvaluation X d U z p θ y).toAlternatingMap.map_linearDependent _ fun hli ↦ ?_
  have hcard := hli.fintype_card_le_finrank
  rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hcard
  lia

lemma holomorphicFormRelations_eq_restrictionStableAnalyticKernel
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ) :
    holomorphicFormRelations X d U p = restrictionStableAnalyticKernel X d U p := rfl

lemma holomorphicFormRelations_eq_top_of_lt [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    {p : ℕ} (hp : d < p) : holomorphicFormRelations X d U p = ⊤ := by
  refine top_unique fun θ _ ↦ ?_
  rw [holomorphicFormRelations, restrictionStableAnalyticKernel]
  simp only [Submodule.mem_iInf, Submodule.mem_comap]
  intro V i
  rw [chartEvaluationKernel_eq_top_of_lt X d V hp]
  trivial

lemma holomorphicForm_eq_zero_of_lt [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    {p : ℕ} (hp : d < p) (θ : HolomorphicForm X d U p) : θ = 0 := by
  obtain ⟨θ, rfl⟩ := Submodule.mkQ_surjective (holomorphicFormRelations X d U p) θ
  change Submodule.Quotient.mk θ = 0
  rw [Submodule.Quotient.mk_eq_zero, holomorphicFormRelations_eq_top_of_lt X d U hp]
  trivial

lemma holomorphicFormDifferential_squared [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ)
    (θ : HolomorphicForm X d U p) :
    holomorphicFormDifferential X d U (p + 1)
      (holomorphicFormDifferential X d U p θ) = 0 := by
  obtain ⟨θ, rfl⟩ := Submodule.mkQ_surjective (holomorphicFormRelations X d U p) θ
  change Submodule.Quotient.mk
    (Algebra.DeRham.differential ℂ (OpenHolomorphicFunctions X d U) (p + 1)
      (Algebra.DeRham.differential ℂ (OpenHolomorphicFunctions X d U) p θ)) = 0
  rw [Algebra.DeRham.differential_squared]
  exact Submodule.Quotient.mk_zero _

lemma holomorphicFormRestriction_differential [SmoothOfRelativeDimension d X.hom]
    {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} (i : U ⟶ V) (p : ℕ)
    (θ : HolomorphicForm X d U p) :
    holomorphicFormRestriction X d i (p + 1)
        (holomorphicFormDifferential X d U p θ) =
      holomorphicFormDifferential X d V p
        (holomorphicFormRestriction X d i p θ) := by
  obtain ⟨θ, rfl⟩ := Submodule.mkQ_surjective (holomorphicFormRelations X d U p) θ
  change Submodule.Quotient.mk
      (formRestriction X d i (p + 1)
        (Algebra.DeRham.differential ℂ (OpenHolomorphicFunctions X d U) p θ)) =
    Submodule.Quotient.mk
      (Algebra.DeRham.differential ℂ (OpenHolomorphicFunctions X d V) p
        (formRestriction X d i p θ))
  rw [formRestriction_differential]

end AlgebraicGeometry.ComplexPoint
