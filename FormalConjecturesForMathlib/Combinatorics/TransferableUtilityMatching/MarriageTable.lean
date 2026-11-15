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

public import Mathlib.Data.NNReal.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Marriage tables with singlehood

A marriage table records nonnegative masses of marriages and singles on each side. Its two
population margins are separate and may have different totals. Singlehood is represented by
`none` in each side's option accessor; there is no outside–outside cell.

`PositiveMarriageTable` restricts both double-odds-ratio families to strictly positive entries.
`surplusContrast` is the double difference of a real-valued surplus matrix.

## References

* Galichon and Salanié, [*Labeling Dependence in Separable Matching Markets*]
  (https://bsalanie.github.io/files/MatchingIIL_9dec2019.pdf), Property 2, p. 7.
* Chiappori, Nguyen, and Salanié, [*The Econometrics of Matching with Transferable Utility:
  A Progress Report*](https://dlinh-n.github.io/f/wp/CNS12April2026.pdf), §3.2.1, p. 11.
-/

@[expose] public section

open scoped BigOperators NNReal

namespace TransferableUtilityMatching

/-- Nonnegative marriage and singlehood masses for two sets of observed types. -/
@[ext]
structure MarriageTable (X Y : Type*) where
  marriages : X → Y → ℝ≥0
  singleMen : X → ℝ≥0
  singleWomen : Y → ℝ≥0

namespace MarriageTable

variable {X Y : Type*}

/-- A man's option is a woman's type or singlehood. -/
def menCell (μ : MarriageTable X Y) (x : X) : Option Y → ℝ≥0
  | none => μ.singleMen x
  | some y => μ.marriages x y

/-- A woman's option is a man's type or singlehood. -/
def womenCell (μ : MarriageTable X Y) : Option X → Y → ℝ≥0
  | none, y => μ.singleWomen y
  | some x, y => μ.marriages x y

@[simp]
lemma menCell_none (μ : MarriageTable X Y) (x : X) : μ.menCell x none = μ.singleMen x := rfl

@[simp]
lemma menCell_some (μ : MarriageTable X Y) (x : X) (y : Y) :
    μ.menCell x (some y) = μ.marriages x y := rfl

@[simp]
lemma womenCell_none (μ : MarriageTable X Y) (y : Y) : μ.womenCell none y = μ.singleWomen y :=
  rfl

@[simp]
lemma womenCell_some (μ : MarriageTable X Y) (x : X) (y : Y) :
    μ.womenCell (some x) y = μ.marriages x y := rfl

/-- The marriages and singles exhaust each type's population, separately on each side. -/
def HasMargins [Fintype X] [Fintype Y] (μ : MarriageTable X Y)
    (n : X → ℝ≥0) (m : Y → ℝ≥0) : Prop :=
  (∀ x, (∑ y, μ.marriages x y) + μ.singleMen x = n x) ∧
    ∀ y, (∑ x, μ.marriages x y) + μ.singleWomen y = m y

/-- Interchange the two sides, including their singles. -/
def transpose (μ : MarriageTable X Y) : MarriageTable Y X where
  marriages y x := μ.marriages x y
  singleMen := μ.singleWomen
  singleWomen := μ.singleMen

@[simp]
lemma transpose_marriages (μ : MarriageTable X Y) (y : Y) (x : X) :
    μ.transpose.marriages y x = μ.marriages x y := rfl

@[simp]
lemma transpose_singleMen (μ : MarriageTable X Y) (y : Y) :
    μ.transpose.singleMen y = μ.singleWomen y := rfl

@[simp]
lemma transpose_singleWomen (μ : MarriageTable X Y) (x : X) :
    μ.transpose.singleWomen x = μ.singleMen x := rfl

@[simp]
lemma transpose_transpose (μ : MarriageTable X Y) : μ.transpose.transpose = μ := rfl

@[simp]
lemma menCell_transpose (μ : MarriageTable X Y) (y : Y) (x : Option X) :
    μ.transpose.menCell y x = μ.womenCell x y := by
  cases x <;> rfl

@[simp]
lemma womenCell_transpose (μ : MarriageTable X Y) (y : Option Y) (x : X) :
    μ.transpose.womenCell y x = μ.menCell x y := by
  cases y <;> rfl

@[simp]
lemma hasMargins_transpose_iff [Fintype X] [Fintype Y] (μ : MarriageTable X Y)
    (n : X → ℝ≥0) (m : Y → ℝ≥0) : μ.transpose.HasMargins m n ↔ μ.HasMargins n m :=
  and_comm

/-- The feasible table in which everybody remains single. -/
def allSingles (n : X → ℝ≥0) (m : Y → ℝ≥0) : MarriageTable X Y where
  marriages _ _ := 0
  singleMen := n
  singleWomen := m

@[simp]
lemma allSingles_hasMargins [Fintype X] [Fintype Y] (n : X → ℝ≥0) (m : Y → ℝ≥0) :
    (allSingles n m).HasMargins n m := by
  simp [HasMargins, allSingles]

/-- Every marriage and both kinds of singles have strictly positive mass. -/
def IsPositive (μ : MarriageTable X Y) : Prop :=
  (∀ x y, 0 < μ.marriages x y) ∧ (∀ x, 0 < μ.singleMen x) ∧ ∀ y, 0 < μ.singleWomen y

lemma IsPositive.menCell_pos {μ : MarriageTable X Y} (h : μ.IsPositive)
    (x : X) (y : Option Y) : 0 < μ.menCell x y := by
  cases y with
  | none => exact h.2.1 x
  | some y => exact h.1 x y

lemma IsPositive.womenCell_pos {μ : MarriageTable X Y} (h : μ.IsPositive)
    (x : Option X) (y : Y) : 0 < μ.womenCell x y := by
  cases x with
  | none => exact h.2.2 y
  | some x => exact h.1 x y

@[simp]
lemma isPositive_transpose_iff (μ : MarriageTable X Y) :
    μ.transpose.IsPositive ↔ μ.IsPositive := by
  simp only [IsPositive, transpose]
  constructor
  · rintro ⟨h, hw, hm⟩
    exact ⟨fun x y ↦ h y x, hm, hw⟩
  · rintro ⟨h, hm, hw⟩
    exact ⟨fun y x ↦ h x y, hw, hm⟩

noncomputable section

/-- Multiply every mass, including singles, by the same nonnegative factor. -/
def scale (c : ℝ≥0) (μ : MarriageTable X Y) : MarriageTable X Y where
  marriages x y := c * μ.marriages x y
  singleMen x := c * μ.singleMen x
  singleWomen y := c * μ.singleWomen y

@[simp]
lemma scale_marriages (c : ℝ≥0) (μ : MarriageTable X Y) (x : X) (y : Y) :
    (μ.scale c).marriages x y = c * μ.marriages x y := rfl

@[simp]
lemma scale_singleMen (c : ℝ≥0) (μ : MarriageTable X Y) (x : X) :
    (μ.scale c).singleMen x = c * μ.singleMen x := rfl

@[simp]
lemma scale_singleWomen (c : ℝ≥0) (μ : MarriageTable X Y) (y : Y) :
    (μ.scale c).singleWomen y = c * μ.singleWomen y := rfl

@[simp]
lemma menCell_scale (c : ℝ≥0) (μ : MarriageTable X Y) (x : X) (y : Option Y) :
    (μ.scale c).menCell x y = c * μ.menCell x y := by
  cases y <;> rfl

@[simp]
lemma womenCell_scale (c : ℝ≥0) (μ : MarriageTable X Y) (x : Option X) (y : Y) :
    (μ.scale c).womenCell x y = c * μ.womenCell x y := by
  cases x <;> rfl

@[simp]
lemma scale_transpose (c : ℝ≥0) (μ : MarriageTable X Y) :
    μ.transpose.scale c = (μ.scale c).transpose := rfl

lemma HasMargins.scale [Fintype X] [Fintype Y] {μ : MarriageTable X Y}
    {n : X → ℝ≥0} {m : Y → ℝ≥0} (h : μ.HasMargins n m) (c : ℝ≥0) :
    (μ.scale c).HasMargins (fun x ↦ c * n x) (fun y ↦ c * m y) := by
  constructor
  · intro x
    simpa only [scale_marriages, scale_singleMen, ← Finset.mul_sum, ← mul_add] using
      congrArg (c * ·) (h.1 x)
  · intro y
    simpa only [scale_marriages, scale_singleWomen, ← Finset.mul_sum, ← mul_add] using
      congrArg (c * ·) (h.2 y)

lemma IsPositive.scale {μ : MarriageTable X Y} (h : μ.IsPositive) {c : ℝ≥0}
    (hc : 0 < c) : (μ.scale c).IsPositive :=
  ⟨fun x y ↦ mul_pos hc (h.1 x y), fun x ↦ mul_pos hc (h.2.1 x),
    fun y ↦ mul_pos hc (h.2.2 y)⟩

end

end MarriageTable

/-- Marriage tables on which all marital-option odds have positive denominators. -/
abbrev PositiveMarriageTable (X Y : Type*) := {μ : MarriageTable X Y // μ.IsPositive}

namespace PositiveMarriageTable

variable {X Y : Type*}

/-- Interchange the two sides of a strictly positive table. -/
def transpose (μ : PositiveMarriageTable X Y) : PositiveMarriageTable Y X :=
  ⟨μ.val.transpose, (MarriageTable.isPositive_transpose_iff _).2 μ.property⟩

@[simp]
lemma transpose_val (μ : PositiveMarriageTable X Y) : μ.transpose.val = μ.val.transpose := rfl

@[simp]
lemma transpose_transpose (μ : PositiveMarriageTable X Y) : μ.transpose.transpose = μ := by
  apply Subtype.ext
  rfl

noncomputable section

/-- Compare two men's types and two of their marital options, including singlehood. -/
def menDoubleOdds (μ : PositiveMarriageTable X Y) (x z : X) (y t : Option Y) : ℝ≥0 :=
  μ.val.menCell x y * μ.val.menCell z t / (μ.val.menCell x t * μ.val.menCell z y)

/-- Compare two women's types and two of their marital options, including singlehood. -/
def womenDoubleOdds (μ : PositiveMarriageTable X Y) (x z : Option X) (y t : Y) : ℝ≥0 :=
  μ.val.womenCell x y * μ.val.womenCell z t / (μ.val.womenCell x t * μ.val.womenCell z y)

lemma menDoubleOdds_pos (μ : PositiveMarriageTable X Y) (x z : X) (y t : Option Y) :
    0 < μ.menDoubleOdds x z y t :=
  div_pos (mul_pos (μ.property.menCell_pos x y) (μ.property.menCell_pos z t))
    (mul_pos (μ.property.menCell_pos x t) (μ.property.menCell_pos z y))

lemma womenDoubleOdds_pos (μ : PositiveMarriageTable X Y) (x z : Option X) (y t : Y) :
    0 < μ.womenDoubleOdds x z y t :=
  div_pos (mul_pos (μ.property.womenCell_pos x y) (μ.property.womenCell_pos z t))
    (mul_pos (μ.property.womenCell_pos x t) (μ.property.womenCell_pos z y))

@[simp]
lemma menDoubleOdds_transpose (μ : PositiveMarriageTable X Y) (y t : Y) (x z : Option X) :
    μ.transpose.menDoubleOdds y t x z = μ.womenDoubleOdds x z y t := by
  simp only [menDoubleOdds, womenDoubleOdds, transpose_val, MarriageTable.menCell_transpose]
  rw [mul_comm (μ.val.womenCell z y)]

@[simp]
lemma womenDoubleOdds_transpose (μ : PositiveMarriageTable X Y) (y t : Option Y) (x z : X) :
    μ.transpose.womenDoubleOdds y t x z = μ.menDoubleOdds x z y t := by
  simp only [menDoubleOdds, womenDoubleOdds, transpose_val, MarriageTable.womenCell_transpose]
  rw [mul_comm (μ.val.menCell z y)]

/-- Positive common scaling stays in the positive domain. -/
def scale (c : ℝ≥0) (hc : 0 < c) (μ : PositiveMarriageTable X Y) :
    PositiveMarriageTable X Y :=
  ⟨μ.val.scale c, μ.property.scale hc⟩

@[simp]
lemma scale_val (c : ℝ≥0) (hc : 0 < c) (μ : PositiveMarriageTable X Y) :
    (μ.scale c hc).val = μ.val.scale c := rfl

@[simp]
lemma menDoubleOdds_scale (c : ℝ≥0) (hc : 0 < c) (μ : PositiveMarriageTable X Y)
    (x z : X) (y t : Option Y) : (μ.scale c hc).menDoubleOdds x z y t =
      μ.menDoubleOdds x z y t := by
  simp only [menDoubleOdds, scale_val, MarriageTable.menCell_scale]
  rw [mul_mul_mul_comm c _ c _, mul_mul_mul_comm c _ c _,
    mul_div_mul_left _ _ (mul_ne_zero hc.ne' hc.ne')]

@[simp]
lemma womenDoubleOdds_scale (c : ℝ≥0) (hc : 0 < c) (μ : PositiveMarriageTable X Y)
    (x z : Option X) (y t : Y) : (μ.scale c hc).womenDoubleOdds x z y t =
      μ.womenDoubleOdds x z y t := by
  simp only [womenDoubleOdds, scale_val, MarriageTable.womenCell_scale]
  rw [mul_mul_mul_comm c _ c _, mul_mul_mul_comm c _ c _,
    mul_div_mul_left _ _ (mul_ne_zero hc.ne' hc.ne')]

end

end PositiveMarriageTable

/-- The $2\times2$ double difference of systematic surplus. -/
def surplusContrast {X Y : Type*} (Φ : X → Y → ℝ) (x z : X) (y t : Y) : ℝ :=
  Φ x y + Φ z t - Φ x t - Φ z y

@[simp]
lemma surplusContrast_transpose {X Y : Type*} (Φ : X → Y → ℝ) (x z : X) (y t : Y) :
    surplusContrast (fun y x ↦ Φ x y) y t x z = surplusContrast Φ x z y t := by
  unfold surplusContrast
  ring

namespace MarriageTable

/-- A positive $2\times2$ table with unit mass in every marriage and singles cell. -/
def unitTwoByTwo : MarriageTable (Fin 2) (Fin 2) where
  marriages _ _ := 1
  singleMen _ := 1
  singleWomen _ := 1

lemma unitTwoByTwo_isPositive : unitTwoByTwo.IsPositive := by
  norm_num [IsPositive, unitTwoByTwo]

lemma unitTwoByTwo_hasMargins : unitTwoByTwo.HasMargins (fun _ ↦ 3) (fun _ ↦ 3) := by
  norm_num [HasMargins, unitTwoByTwo]

end MarriageTable

end TransferableUtilityMatching
