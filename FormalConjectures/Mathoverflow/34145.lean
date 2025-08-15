/-
Copyright 2025 The Formal Conjectures Authors.

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

import FormalConjectures.Util.ProblemImports

open Real MeasureTheory Measure

/-!
# Mathoverflow 34145

Can the unit square be covered by (1/k)-by-(1/(k+1)) rectangles (across 1 ≤ k natural)?

I am deliberately not requiring that the rotations can only be 0ᵒ, 90ᵒ, 180ᵒ, or 270ᵒ.

Because of indexing, since `n : ℕ` starts at 0, we change the side lengths to `1 / (n + 1)` and
`1 / (n + 2)`, so that the first rectangle is `1/1` by `1/2`, the second is `1/2` by `1/3`, etc.

*Reference:* [mathoverflow/34145](https://mathoverflow.net/q/34145)
asked by user [*Kaveh*](https://mathoverflow.net/users/7507/kaveh)
-/

/-- A rectangle is specified by its width, height, starting point, and rotation.
The rectangle is assumed to start in the lower left corner. For example, the unit square
`{ (x, y) | 0 ≤ x ≤ 1, 0 ≤ y ≤ 1 }` is specified as `⟨1, 1, (0, 0), 0⟩`  -/
structure Rectangle : Type where
  width : ℝ
  height : ℝ
  start : ℝ × ℝ
  rotation : Angle

/-- A combination of a rotation and a translation to map the standard rectangle to the desired
rectangle.
-/
noncomputable def rigidMotion (start : ℝ × ℝ) (θ : Angle) (p : ℝ × ℝ) : (ℝ × ℝ) :=
  (start.1 + p.1 * θ.cos - p.2 * θ.sin, start.2 + p.1 * θ.sin + p.2 * θ.cos)

@[category test, AMS 51]
lemma rigidMotion_test : rigidMotion (sqrt 2, sqrt 11) (2 * π / 3 : ℝ) (sqrt 5, sqrt 7) =
    (sqrt 2 - sqrt 5 / 2 - sqrt 21 / 2, -sqrt 7 / 2 + sqrt 11 + sqrt 15 / 2) := by
  simp [rigidMotion, mul_div_assoc, cos_two_mul, sin_two_mul,
    show (21 : ℝ) = 3 * 7 by norm_num, show (15 : ℝ) = 3 * 5 by norm_num]
  ring_nf; simp

/-- A scaling to map the unit square to a standard rectangle. -/
noncomputable def scale (x y : ℝ) (p : ℝ × ℝ) : (ℝ × ℝ) :=
  (x * p.1, y * p.2)

/-- The unit square. -/
def unitSquare : Set (ℝ × ℝ) :=
  { p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 }

/-- Converts a rectangle to a set in `ℝ × ℝ`. -/
def Rectangle.toSet (r : Rectangle) : Set (ℝ × ℝ) :=
  rigidMotion r.start r.rotation '' (scale r.width r.height '' unitSquare)

/-- The standard Lebesgue measure on `ℝ²`. -/
noncomputable abbrev lbMeasure : Measure (ℝ × ℝ) :=
  (Basis.finTwoProd ℝ).addHaar

/-- `lbMeasure` is invariant under `rigidMotion start θ`. -/
@[category test, AMS 51]
lemma lbMeasure_rigidMotion (start : ℝ × ℝ) (θ : Angle) (s : Set (ℝ × ℝ)) :
    lbMeasure (rigidMotion start θ '' s) = lbMeasure s := by
  let α (x : ℝ × ℝ) := (x.1 * θ.cos - x.2 * θ.sin, x.1 * θ.sin + x.2 * θ.cos)
  trans (Basis.finTwoProd _).addHaar (α '' s)
  · exact (measure_preimage_add_right _ start _).symm.trans (congr_arg _ (Set.ext <| by
      simp [rigidMotion, α, add_sub_assoc, add_assoc, Prod.ext_iff, ← eq_sub_iff_add_eq']))
  · let β := Basis.finTwoProd ℝ
    trans β.addHaar (β.constr ℝ ![α (β 0), α (β 1)] '' s)
    · exact congr_arg _ <| Set.image_congr <| by aesop
    · rw [addHaar_image_linearMap, eq_comm, ← LinearMap.det_toMatrix β, Matrix.det_fin_two]
      simp [α, β, LinearMap.toMatrix_apply, ← sq]

/-- `lbMeasure` is scaled by `scale`. -/
@[category test, AMS 51]
lemma lbMeasure_scale (x y : ℝ) (s : Set (ℝ × ℝ)) :
    lbMeasure (scale x y '' s) = .ofReal |x * y| * lbMeasure s := by
  let scaleLinear : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  { toFun p := (x * p.1, y * p.2)
    map_add' p q := by simp [mul_add]
    map_smul' c p := by simp [mul_left_comm] }
  have h₁ : scale x y = scaleLinear := rfl
  have h₂ : scaleLinear.toMatrix (Basis.finTwoProd ℝ) (Basis.finTwoProd ℝ) = !![x, 0; 0, y] := by
    ext i j; unfold scaleLinear; fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix_apply]
  simp [h₁, ← LinearMap.det_toMatrix (Basis.finTwoProd ℝ), h₂]

/-- The Lebesgue measure of the unit square is `1`. -/
@[category test, AMS 51]
lemma lbMeasure_unitSquare : lbMeasure unitSquare = 1 := by
  convert (Basis.addHaar_eq_iff (Basis.finTwoProd ℝ) _).1 rfl
  ext p
  simp only [unitSquare, Set.mem_setOf_eq, Basis.coe_parallelepiped, mem_parallelepiped_iff,
    Set.mem_Icc, Fin.sum_univ_two, Fin.isValue, Basis.finTwoProd_zero, Prod.smul_mk, smul_eq_mul,
    mul_one, mul_zero, Basis.finTwoProd_one, Prod.mk_add_mk, add_zero, zero_add, Pi.le_def]
  exact ⟨fun h ↦ ⟨![p.1, p.2], by simp [Fin.forall_fin_succ, h]⟩,
    fun ⟨t, ht⟩ ↦ ht.2 ▸ ⟨ht.1.1 0, ht.1.2 0, ht.1.1 1, ht.1.2 1⟩⟩

/-- The Lebesgue measure of the a rectangle `r` is `r.width * r.height` -/
@[category test, AMS 51]
lemma lbMeasure_rectangle_toSet (r : Rectangle) :
    lbMeasure r.toSet = .ofReal |r.width * r.height| := by
  rw [Rectangle.toSet, lbMeasure_rigidMotion, lbMeasure_scale, lbMeasure_unitSquare, mul_one]

/-- The areas of the required rectangles sum to 1. -/
@[category test, AMS 51]
lemma tsum_area_eq_one : ∑' (n : ℕ), ((1 / (n + 1)) * (1 / (n + 2)) : ℝ) = 1 := by
  have (n : ℕ) : ∑ i ∈ Finset.range n, (1 / (i + 1) * (1 / (i + 2)) : ℝ) = 1 - 1 / (n + 1) := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; field_simp; ring
  refine HasSum.tsum_eq ((hasSum_iff_tendsto_nat_of_nonneg (fun i ↦ ?_) _).2 ?_)
  · positivity
  · simp_rw [this]
    convert tendsto_one_div_add_atTop_nhds_zero_nat.const_sub (1 : ℝ) (c := 0) using 1
    norm_num

/-- A configuration of rectangles of sides `1 / (n + 1)` and `1 / (n + 2)`. -/
structure Configuration : Type where
  rect (n : ℕ) : Rectangle
  rect_width (n : ℕ) : (rect n).width = 1 / (n + 1)
  rect_height (n : ℕ) : (rect n).height = 1 / (n + 2)

/-- A "packing" means that the interiors of any two rectangles are disjoint. -/
def Configuration.IsPacking (c : Configuration) : Prop :=
  Pairwise fun m n ↦ interior (c.rect m).toSet ∩ interior (c.rect n).toSet = ∅

/-- Can a unit square be covered by rectangles of width `1 / (n + 1)` and height `1 / (n + 2)`? -/
@[category research open, AMS 51]
theorem rectangles_cover_unit_square :
    (∃ c : Configuration, ∀ p ∈ unitSquare, ∃ n, p ∈ (c.rect n).toSet) ↔ answer(sorry) := by
  sorry

/-- Equivalently, can a unit square be packed with rectangles of width `1 / (n + 1)` and height
`1 / (n + 2)`? -/
@[category research open, AMS 51]
theorem rectangles_pack_unit_square :
    (∃ c : Configuration, (∀ n, (c.rect n).toSet ⊆ unitSquare) ∧ c.IsPacking) ↔ answer(sorry) := by
  sorry

/-- It is known that packing the rectangles into a square of side length `133/132` is possible.

Reference: https://www.sciencedirect.com/science/article/pii/0097316594901163
-/
@[category research solved, AMS 51]
theorem rectangles_pack_square_133_div_132 :
    (∃ c : Configuration,
      (∀ n, (c.rect n).toSet ⊆ Rectangle.toSet ⟨133/132, 133/132, (0, 0), 0⟩) ∧
      c.IsPacking) := by
  sorry

/-- It is known that packing the rectangles into a square of side length `501/500` is possible.

Reference: https://www.sciencedirect.com/science/article/pii/S0167506008706009
-/
@[category research solved, AMS 51]
theorem rectangles_pack_square_501_div_500 :
    (∃ c : Configuration,
      (∀ n, (c.rect n).toSet ⊆ Rectangle.toSet ⟨501/500, 501/500, (0, 0), 0⟩) ∧
      c.IsPacking) := by
  sorry
