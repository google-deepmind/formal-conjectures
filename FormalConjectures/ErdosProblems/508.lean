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
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Erdős Problem 508

*Reference:* [erdosproblems.com/508](https://www.erdosproblems.com/508)
-/



namespace Erdos508

open Real

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/--
Whether c defines a valid coloring of the plane, i.e. whether
c(x₁) ≠ c(x₂) holds for all points x₁ ∈ ℝ² and x₂ ∈ ℝ² that are
exactly distance 1 apart from each other (with respect to
the euclidean metric)
-/
@[category API, AMS 5]
def validColoring {n : ℕ} (c : Plane → Fin n) : Prop :=
  ∀ x₁ x₂, dist x₁ x₂ = 1 → c x₁ ≠ c x₂

/--
Whether the `Plane` is colorable with n colors
-/
@[category API, AMS 5]
def planeIsColorableWith (n : ℕ) : Prop :=
  ∃ c : Plane → Fin n, validColoring c


/-
The smallest number n ∈ ℕ such that the "`Plane` is colorable"
with n colors, i.e. there is a coloring c : ℝ × ℝ → Fin n
such that c(x₁) ≠ c(x₂) holds for all x₁,x₂ ∈ ℝ² that are
distance 1 apart with respect to the euclidean metric
--/
@[category research open, AMS 5]
noncomputable def chromaticNumberOfThePlane : WithTop ℕ :=
sInf ((↑) '' { n : ℕ | planeIsColorableWith n})


scoped notation "χ(ℝ²)" => chromaticNumberOfThePlane


/--
This upper bound for the chromatic number of the plane was
observed by John R. Isbell. His approach was dividing the
plane into hexagons of uniform size and coloring them with a repeating
pattern. A proof can probably be found in:

Soifer, Alexander (2008), The Mathematical Coloring Book: Mathematics of Coloring and the Colorful Life of its Creators, New York: Springer, ISBN 978-0-387-74640-1

An alternative approach that uses square tiling was highlighted by László Székely.
-/
@[category research solved, AMS 5]
def planeIs7Colorable : planeIsColorableWith 7 :=
  by sorry


/--
The "chromatic number of the `Plane`" is at least 3. This is proven
by considering an equilateral triangle in the plane.
-/
@[category undergraduate, AMS 5]
theorem chromaticNumberOfThePlaneGeq3 : 3 ≤ χ(ℝ²) := by
  unfold chromaticNumberOfThePlane
  apply le_sInf
  intro x plane_is_x_colorable


  by_cases x_is_top_case : x = ⊤
  -- If x is the top 3 ≤ x holds trivially
  · rw [x_is_top_case]
    exact OrderTop.le_top 3

  · obtain ⟨x₀, ⟨plane_is_x₀_colorable, x₀_equ_x⟩⟩ := plane_is_x_colorable

    -- Define the points p₁, p₂ and p₃ of an arbitrary equilateral triangle
    let p₁ : Plane := ![0, 0]
    let p₂ : Plane := ![1, 0]
    let p₃ : Plane := ![0.5, Real.sqrt 3 / 2]

    -- Prove that the points are exactly distance 1 apart from each other
    have unit_dist_p₁_p₂ : dist p₁ p₂ = 1 := by simp [p₁, p₂, dist]
    have unit_dist_p₂_p₃ : dist p₂ p₃ = 1 := by
      simp [p₂, p₃, dist, div_pow]
      norm_num
    have unit_dist_p₁_p₃ : dist p₁ p₃ = 1 := by
      simp [p₁, p₃,  dist, div_pow]
      norm_num

    obtain ⟨coloring, coloring_is_valid⟩ := plane_is_x₀_colorable
    unfold validColoring at coloring_is_valid

    -- We'll denote coloring p_i with c_i (for i ∈ {1,2,3})
    -- Prove that p₁, p₂ and p₃ have different images under the coloring
    have not_c₁_equ_c₂ : coloring p₁ ≠ coloring p₂ := (coloring_is_valid p₁ p₂ unit_dist_p₁_p₂)
    have not_c₂_equ_c₃ : coloring p₂ ≠ coloring p₃ := (coloring_is_valid p₂ p₃ unit_dist_p₂_p₃)
    have not_c₁_equ_c₃ : coloring p₁ ≠ coloring p₃ := (coloring_is_valid p₁ p₃ unit_dist_p₁_p₃)


    let image_subset : Finset (Fin x₀) := {coloring p₁, coloring p₂, coloring p₃}

    -- Prove that |image_subset| = 3
    have image_subset_card_equ_3 : image_subset.card = 3 := by
      rw [Finset.card_eq_three]
      use (coloring p₁)
      use (coloring p₂)
      use (coloring p₃)

    have _3_leq_x₀ :=
    calc
      3 = image_subset.card := image_subset_card_equ_3.symm
      _ ≤ Fintype.card (Fin x₀) := by exact Finset.card_le_univ image_subset
      _ = x₀ := by exact Fintype.card_fin x₀

    rw [← x₀_equ_x]
    exact Nat.ofNat_le_cast.mpr _3_leq_x₀


/--
The "chromatic number of the plane" is at least 4. This can be
proven by considering the [Moser-Spindel graph](https://de.wikipedia.org/wiki/Moser-Spindel)
or the [Golomb graph](https://en.wikipedia.org/wiki/Golomb_graph) graph.
-/
@[category research solved, AMS 5]
theorem chromaticNumberOfThePlaneGeq4 : 4 ≤ χ(ℝ²) := by
  sorry

/--
Aubrey de Grey proved this tighter lower bound in 2018 using a graph that has >1000 nodes.

"The chromatic number of the plane is at least 5" Aubrey D. N. J. de Grey, 2018
(https://doi.org/10.48550/arXiv.1804.02385)
-/
@[category research solved, AMS 5]
theorem chromaticNumberOfThePlaneGeq5 : 5 ≤ χ(ℝ²) := by
  sorry
