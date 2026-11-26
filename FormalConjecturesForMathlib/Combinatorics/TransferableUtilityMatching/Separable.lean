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

public import FormalConjecturesForMathlib.Combinatorics.TransferableUtilityMatching.MarriageTable
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.NullMeasurable
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

/-!
# Separable transferable-utility matching

A type-conditional joint law describes the tastes for all marital options, including singles.
Random-utility choice probabilities and market clearing define the equilibrium table.
The systematic utilities for singlehood are zero; its random taste remains a coordinate of the law.

## References

* Galichon and Salanié, [*Labeling Dependence in Separable Matching Markets*]
  (https://bsalanie.github.io/files/MatchingIIL_9dec2019.pdf), Assumption 1 and Property 2.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace TransferableUtilityMatching

namespace RandomUtility

variable {A : Type*}

/-- The taste vectors for which option `a` maximizes utility. -/
def choiceEvent (u : A → ℝ) (a : A) : Set (A → ℝ) :=
  {ε | ∀ b, u b + ε b ≤ u a + ε a}

lemma measurableSet_choiceEvent [Fintype A] (u : A → ℝ) (a : A) :
    MeasurableSet (choiceEvent u a) := by
  simp only [choiceEvent, Set.ofPred_forall]
  exact MeasurableSet.iInter fun b ↦
    measurableSet_le (measurable_const.add (measurable_pi_apply b))
      (measurable_const.add (measurable_pi_apply a))

/-- Choice probability under a joint taste law. Coordinates need not be independent. -/
noncomputable def choiceProbability (P : ProbabilityMeasure (A → ℝ)) (u : A → ℝ)
    (a : A) : ℝ≥0 := P (choiceEvent u a)

lemma choiceProbability_le_one (P : ProbabilityMeasure (A → ℝ)) (u : A → ℝ) (a : A) :
    choiceProbability P u a ≤ 1 := P.apply_le_one _

/-- All pairwise taste differences are atomless, so fixed utility offsets create no ties. -/
def NoTies (P : ProbabilityMeasure (A → ℝ)) : Prop :=
  ∀ a b, a ≠ b → ∀ c : ℝ, (P : Measure (A → ℝ)) {ε | ε a - ε b = c} = 0

lemma iUnion_choiceEvent [Fintype A] [Nonempty A] (u : A → ℝ) :
    ⋃ a, choiceEvent u a = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro ε
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image Finset.univ (fun a ↦ u a + ε a)
    Finset.univ_nonempty
  exact Set.mem_iUnion.mpr ⟨a, fun b ↦ ha b (Finset.mem_univ b)⟩

lemma NoTies.aedisjoint_choiceEvent {P : ProbabilityMeasure (A → ℝ)} (hP : NoTies P)
    (u : A → ℝ) : Pairwise (Function.onFun (AEDisjoint (P : Measure (A → ℝ)))
      (choiceEvent u)) := by
  intro a b hab
  apply measure_mono_null (t := {ε : A → ℝ | ε a - ε b = u b - u a})
  · rintro ε ⟨ha, hb⟩
    have hab' := ha b
    have hba' := hb a
    dsimp at hab' hba' ⊢
    linarith
  · exact hP a b hab _

lemma sum_choiceProbability [Fintype A] [Nonempty A] {P : ProbabilityMeasure (A → ℝ)}
    (hP : NoTies P) (u : A → ℝ) : ∑ a, choiceProbability P u a = 1 := by
  have h := measure_iUnion₀ (hP.aedisjoint_choiceEvent u)
    (fun a ↦ (measurableSet_choiceEvent u a).nullMeasurableSet)
  rw [iUnion_choiceEvent, measure_univ, tsum_fintype] at h
  apply ENNReal.coe_injective
  simpa [choiceProbability, ENNReal.ofNNReal_finsetSum] using h.symm

/-- A constant shift of all deterministic utilities leaves choices unchanged. -/
lemma choiceEvent_add_const (u : A → ℝ) (a : A) (c : ℝ) :
    choiceEvent (fun b ↦ u b + c) a = choiceEvent u a := by
  ext ε
  simp only [choiceEvent, Set.mem_ofPred_eq]
  congr! 1
  constructor <;> intro h <;> linarith

end RandomUtility

/-- A demographic vector has a positive population for each observed type on both sides. -/
structure Demographics (X Y : Type*) where
  men : X → ℝ≥0
  women : Y → ℝ≥0
  men_pos : ∀ x, 0 < men x
  women_pos : ∀ y, 0 < women y

namespace Demographics

variable {X Y : Type*}

/-- Multiply both population vectors by the same positive number. -/
noncomputable def scale (d : Demographics X Y) (c : ℝ≥0) (hc : 0 < c) : Demographics X Y where
  men x := c * d.men x
  women y := c * d.women y
  men_pos x := mul_pos hc (d.men_pos x)
  women_pos y := mul_pos hc (d.women_pos y)

/-- Unit populations form an admissible demographic vector for any two type sets. -/
def unit (X Y : Type*) : Demographics X Y where
  men _ := 1
  women _ := 1
  men_pos _ := zero_lt_one
  women_pos _ := zero_lt_one

end Demographics

/-- Fixed systematic surplus and type-conditional joint taste laws for a separable TU model. -/
structure SeparableModel (X Y : Type*) where
  surplus : X → Y → ℝ
  menTastes : X → ProbabilityMeasure (Option Y → ℝ)
  womenTastes : Y → ProbabilityMeasure (Option X → ℝ)

namespace SeparableModel

variable {X Y : Type*}

/-- Extend utilities to the outside option, whose deterministic utility is normalized to zero. -/
def withOutside {A : Type*} (u : A → ℝ) : Option A → ℝ
  | none => 0
  | some a => u a

@[simp] lemma withOutside_zero {A : Type*} : withOutside (0 : A → ℝ) = 0 := by
  funext a
  cases a <;> rfl

@[simp] lemma withOutside_none {A : Type*} (u : A → ℝ) : withOutside u none = 0 := rfl

@[simp] lemma withOutside_some {A : Type*} (u : A → ℝ) (a : A) :
    withOutside u (some a) = u a := rfl

/-- Utilities clear the market and split systematic surplus. Singles retain their own tastes. -/
def IsEquilibrium (M : SeparableModel X Y) (d : Demographics X Y)
    (μ : MarriageTable X Y) : Prop :=
  ∃ U V : X → Y → ℝ,
    (∀ x y, U x y + V x y = M.surplus x y) ∧
    (∀ x y, μ.marriages x y = d.men x * RandomUtility.choiceProbability
      (M.menTastes x) (withOutside (U x)) (some y)) ∧
    (∀ x y, μ.marriages x y = d.women y * RandomUtility.choiceProbability
      (M.womenTastes y) (withOutside (fun x ↦ V x y)) (some x)) ∧
    (∀ x, μ.singleMen x = d.men x * RandomUtility.choiceProbability
      (M.menTastes x) (withOutside (U x)) none) ∧
    (∀ y, μ.singleWomen y = d.women y * RandomUtility.choiceProbability
      (M.womenTastes y) (withOutside (fun x ↦ V x y)) none)

/-- Atomless comparisons and a unique positive equilibrium table for every positive population. -/
def IsAdmissible (M : SeparableModel X Y) : Prop :=
  (∀ x, RandomUtility.NoTies (M.menTastes x)) ∧
  (∀ y, RandomUtility.NoTies (M.womenTastes y)) ∧
  ∀ d : Demographics X Y, ∃! μ : PositiveMarriageTable X Y, M.IsEquilibrium d μ.val

lemma IsEquilibrium.hasMargins [Fintype X] [Fintype Y] {M : SeparableModel X Y}
    (hM : M.IsAdmissible) {d : Demographics X Y} {μ : MarriageTable X Y}
    (h : M.IsEquilibrium d μ) :
    μ.HasMargins d.men d.women := by
  obtain ⟨U, V, _, hm, hw, hs, ht⟩ := h
  constructor
  · intro x
    simp only [hm, hs, ← Finset.mul_sum, ← mul_add]
    have hsum := RandomUtility.sum_choiceProbability (hM.1 x) (withOutside (U x))
    simpa only [Fintype.sum_option, add_comm, mul_one] using congrArg (d.men x * ·) hsum
  · intro y
    simp only [hw, ht, ← Finset.mul_sum, ← mul_add]
    have hsum := RandomUtility.sum_choiceProbability (hM.2.1 y)
      (withOutside (fun x ↦ V x y))
    simpa only [Fintype.sum_option, add_comm, mul_one] using congrArg (d.women y * ·) hsum

lemma IsEquilibrium.scale {M : SeparableModel X Y} {d : Demographics X Y}
    {μ : MarriageTable X Y} (h : M.IsEquilibrium d μ) (c : ℝ≥0) (hc : 0 < c) :
    M.IsEquilibrium (d.scale c hc) (μ.scale c) := by
  obtain ⟨U, V, hΦ, hm, hw, hs, ht⟩ := h
  refine ⟨U, V, hΦ, ?_, ?_, ?_, ?_⟩
  · intro x y
    simpa only [MarriageTable.scale_marriages, Demographics.scale, mul_assoc] using
      congrArg (c * ·) (hm x y)
  · intro x y
    simpa only [MarriageTable.scale_marriages, Demographics.scale, mul_assoc] using
      congrArg (c * ·) (hw x y)
  · intro x
    simpa only [MarriageTable.scale_singleMen, Demographics.scale, mul_assoc] using
      congrArg (c * ·) (hs x)
  · intro y
    simpa only [MarriageTable.scale_singleWomen, Demographics.scale, mul_assoc] using
      congrArg (c * ·) (ht y)

/-- Both families of double odds, including singles, are independent of demographics. -/
def StrongIIA (M : SeparableModel X Y) : Prop :=
  ∀ (d e : Demographics X Y) (μ ν : PositiveMarriageTable X Y),
    M.IsEquilibrium d μ.val → M.IsEquilibrium e ν.val →
      (∀ x z y t, μ.menDoubleOdds x z y t = ν.menDoubleOdds x z y t) ∧
      ∀ x z y t, μ.womenDoubleOdds x z y t = ν.womenDoubleOdds x z y t

/-- With one type on each side, both double-odds families are identically one. -/
lemma strongIIA_of_subsingleton [Subsingleton X] [Subsingleton Y] (M : SeparableModel X Y) :
    M.StrongIIA := by
  have hm (μ : PositiveMarriageTable X Y) (x z : X) (y t : Option Y) :
      μ.menDoubleOdds x z y t = 1 := by
    have hz : z = x := Subsingleton.elim _ _
    subst z
    unfold PositiveMarriageTable.menDoubleOdds
    rw [mul_comm (μ.val.menCell x t), div_self]
    exact mul_ne_zero (μ.property.menCell_pos x y).ne' (μ.property.menCell_pos x t).ne'
  have hw (μ : PositiveMarriageTable X Y) (x z : Option X) (y t : Y) :
      μ.womenDoubleOdds x z y t = 1 := by
    have ht : t = y := Subsingleton.elim _ _
    subst t
    unfold PositiveMarriageTable.womenDoubleOdds
    rw [div_self]
    exact mul_ne_zero (μ.property.womenCell_pos x y).ne' (μ.property.womenCell_pos z y).ne'
  intro d e μ ν _ _
  exact ⟨fun x z y t ↦ (hm μ x z y t).trans (hm ν x z y t).symm,
    fun x z y t ↦ (hw μ x z y t).trans (hw ν x z y t).symm⟩

namespace Examples

/-- A taste vector with one strictly preferred marital option. -/
def favorite (a : Option (Fin 2)) (b : Option (Fin 2)) : ℝ := if b = a then 1 else 0

lemma favorite_mem_choiceEvent (a b : Option (Fin 2)) :
    favorite b ∈ RandomUtility.choiceEvent 0 a ↔ a = b := by
  constructor
  · intro h
    by_contra hab
    have hba := h b
    norm_num [favorite, hab] at hba
  · rintro rfl c
    by_cases hca : c = a <;> simp [favorite, hca]

/-- An equally weighted law of three favorite options. -/
noncomputable def threeFavorites : ProbabilityMeasure (Option (Fin 2) → ℝ) :=
  ⟨(3 : ℝ≥0∞)⁻¹ • (Measure.dirac (favorite none) +
    Measure.dirac (favorite (some 0)) + Measure.dirac (favorite (some 1))), by
    constructor
    simpa [Measure.smul_apply, Measure.add_apply, mul_add] using ENNReal.inv_three_add_inv_three⟩

lemma choiceProbability_threeFavorites (a : Option (Fin 2)) :
    RandomUtility.choiceProbability threeFavorites 0 a = 1 / 3 := by
  classical
  apply ENNReal.coe_injective
  change (threeFavorites (RandomUtility.choiceEvent 0 a) : ℝ≥0∞) = _
  rw [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  simp only [threeFavorites, ProbabilityMeasure.coe_mk, Measure.smul_apply,
    Measure.add_apply, Measure.dirac_apply, Set.indicator_apply, Pi.one_apply, smul_eq_mul,
    favorite_mem_choiceEvent]
  cases a with
  | none => simp
  | some a => fin_cases a <;> simp

/-- A symmetric finite-shock model, used to check all five equilibrium equations. -/
noncomputable def favoriteModel : SeparableModel (Fin 2) (Fin 2) where
  surplus _ _ := 0
  menTastes _ := threeFavorites
  womenTastes _ := threeFavorites

/-- The positive unit table clears symmetric populations of three under the finite-shock model. -/
lemma favoriteModel_isEquilibrium : favoriteModel.IsEquilibrium
    ⟨fun _ ↦ 3, fun _ ↦ 3, fun _ ↦ by norm_num, fun _ ↦ by norm_num⟩
    MarriageTable.unitTwoByTwo := by
  have hz : withOutside (fun _ : Fin 2 ↦ (0 : ℝ)) = 0 := by
    funext a
    cases a <;> rfl
  refine ⟨0, 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    simp [favoriteModel]
  all_goals
    intros
    simp only [Pi.zero_apply, favoriteModel, MarriageTable.unitTwoByTwo]
    simp only [hz, withOutside_zero, choiceProbability_threeFavorites]
    norm_num

end Examples

end SeparableModel

end TransferableUtilityMatching
