import FormalConjectures.Util.ProblemImports
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.SimpleGraph.Coloring

/-!
# Erdős Problem 508

*Reference:* [erdosproblems.com/508](https://www.erdosproblems.com/508)
-/

set_option linter.style.copyright false
set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0

open SimpleGraph
open scoped EuclideanGeometry
open Real

namespace Erdos508

def UnitDistancePlaneGraph : SimpleGraph ℝ² where
  Adj x y := dist x y = 1
  symm _ _ := by simp [_root_.dist_comm]

scoped notation "χ(ℝ²)" => UnitDistancePlaneGraph.chromaticNumber

noncomputable def s3 : ℝ := Real.sqrt 3
@[simp] lemma s3_sq : s3 ^ 2 = 3 := by
  dsimp [s3]; rw [Real.sq_sqrt (by norm_num)]

noncomputable def s11 : ℝ := Real.sqrt 11
@[simp] lemma s11_sq : s11 ^ 2 = 11 := by
  dsimp [s11]; rw [Real.sq_sqrt (by norm_num)]

noncomputable def s33 : ℝ := Real.sqrt 33
@[simp] lemma s33_sq : s33 ^ 2 = 33 := by
  dsimp [s33]; rw [Real.sq_sqrt (by norm_num)]

@[simp] lemma s3_mul_s11 : s3 * s11 = s33 := by
  dsimp [s3, s11, s33]
  rw [← Real.sqrt_mul (by norm_num)]
  congr
  norm_num

noncomputable def moser_points : Fin 7 → ℝ²
  | 0 => !₂[0, 0]
  | 1 => !₂[s3 / 2, -1 / 2]
  | 2 => !₂[s3 / 2, 1 / 2]
  | 3 => !₂[s3, 0]
  | 4 => !₂[(5 * s3 + s11) / 12, (s33 - 5) / 12]
  | 5 => !₂[(5 * s3 - s11) / 12, (s33 + 5) / 12]
  | 6 => !₂[5 * s3 / 6, s33 / 6]

lemma check_edge (u v : Fin 7) (h_sq : dist (moser_points u) (moser_points v) ^ 2 = 1) :
    UnitDistancePlaneGraph.Adj (moser_points u) (moser_points v) := by
  dsimp [UnitDistancePlaneGraph]
  have h1 : Real.sqrt (dist (moser_points u) (moser_points v) ^ 2) = Real.sqrt 1 := by rw [h_sq]
  have h2 : Real.sqrt (dist (moser_points u) (moser_points v) ^ 2) = dist (moser_points u) (moser_points v) := Real.sqrt_sq dist_nonneg
  have h3 : Real.sqrt 1 = (1:ℝ) := Real.sqrt_one
  rw [h2, h3] at h1
  exact h1

lemma edge01 : UnitDistancePlaneGraph.Adj (moser_points 0) (moser_points 1) := by
  apply check_edge; rw [EuclideanSpace.dist_sq_eq_sum]; dsimp [moser_points]
  ring_nf; try simp only [s3_sq, s11_sq, s33_sq, s3_mul_s11]
  try ring
lemma edge02 : UnitDistancePlaneGraph.Adj (moser_points 0) (moser_points 2) := by
  apply check_edge; rw [EuclideanSpace.dist_sq_eq_sum]; dsimp [moser_points]
  ring_nf; try simp only [s3_sq, s11_sq, s33_sq, s3_mul_s11]
  try ring
lemma edge12 : UnitDistancePlaneGraph.Adj (moser_points 1) (moser_points 2) := by
  apply check_edge; rw [EuclideanSpace.dist_sq_eq_sum]; dsimp [moser_points]
  ring_nf; try simp only [s3_sq, s11_sq, s33_sq, s3_mul_s11]
  try ring
lemma edge13 : UnitDistancePlaneGraph.Adj (moser_points 1) (moser_points 3) := by
  apply check_edge; rw [EuclideanSpace.dist_sq_eq_sum]; dsimp [moser_points]
  ring_nf; try simp only [s3_sq, s11_sq, s33_sq, s3_mul_s11]
  try ring
lemma edge23 : UnitDistancePlaneGraph.Adj (moser_points 2) (moser_points 3) := by
  apply check_edge; rw [EuclideanSpace.dist_sq_eq_sum]; dsimp [moser_points]
  ring_nf; try simp only [s3_sq, s11_sq, s33_sq, s3_mul_s11]
  try ring
lemma edge04 : UnitDistancePlaneGraph.Adj (moser_points 0) (moser_points 4) := by
  apply check_edge; rw [EuclideanSpace.dist_sq_eq_sum]; dsimp [moser_points]
  ring_nf; try simp only [s3_sq, s11_sq, s33_sq, s3_mul_s11]
  try ring
lemma edge05 : UnitDistancePlaneGraph.Adj (moser_points 0) (moser_points 5) := by
  apply check_edge; rw [EuclideanSpace.dist_sq_eq_sum]; dsimp [moser_points]
  ring_nf; try simp only [s3_sq, s11_sq, s33_sq, s3_mul_s11]
  try ring
lemma edge45 : UnitDistancePlaneGraph.Adj (moser_points 4) (moser_points 5) := by
  apply check_edge; rw [EuclideanSpace.dist_sq_eq_sum]; dsimp [moser_points]
  ring_nf; try simp only [s3_sq, s11_sq, s33_sq, s3_mul_s11]
  try ring
lemma edge46 : UnitDistancePlaneGraph.Adj (moser_points 4) (moser_points 6) := by
  apply check_edge; rw [EuclideanSpace.dist_sq_eq_sum]; dsimp [moser_points]
  ring_nf; try simp only [s3_sq, s11_sq, s33_sq, s3_mul_s11]
  try ring
lemma edge56 : UnitDistancePlaneGraph.Adj (moser_points 5) (moser_points 6) := by
  apply check_edge; rw [EuclideanSpace.dist_sq_eq_sum]; dsimp [moser_points]
  ring_nf; try simp only [s3_sq, s11_sq, s33_sq, s3_mul_s11]
  try ring
lemma edge36 : UnitDistancePlaneGraph.Adj (moser_points 3) (moser_points 6) := by
  apply check_edge; rw [EuclideanSpace.dist_sq_eq_sum]; dsimp [moser_points]
  ring_nf; try simp only [s3_sq, s11_sq, s33_sq, s3_mul_s11]
  try ring

def is_valid_coloring (c0 c1 c2 c3 c4 c5 c6 : Fin 3) : Bool :=
  c0 != c1 && c0 != c2 && c1 != c2 && c1 != c3 && c2 != c3 &&
  c0 != c4 && c0 != c5 && c4 != c5 && c4 != c6 && c5 != c6 && c3 != c6

theorem no_3_coloring : ∀ c0 c1 c2 c3 c4 c5 c6 : Fin 3, is_valid_coloring c0 c1 c2 c3 c4 c5 c6 = false := by
  decide

/--
The "chromatic number of the plane" is at least 4. This can be
proven by considering the [Moser-Spindel graph](https://de.wikipedia.org/wiki/Moser-Spindel)
or the [Golomb graph](https://en.wikipedia.org/wiki/Golomb_graph) graph.
-/
@[category research formally solved using formal_conjectures at "https://github.com/google-deepmind/formal-conjectures/pull/2422", AMS 5]
theorem HadwigerNelsonAtLeast4 : 4 ≤ χ(ℝ²) := by
  by_contra h
  have h2 : χ(ℝ²) ≤ 3 := by
    cases hx : χ(ℝ²) with
    | top => simp [hx] at h
    | coe a =>
      rw [hx] at h
      norm_cast at h ⊢
      omega
  have hc : UnitDistancePlaneGraph.Colorable 3 := chromaticNumber_le_iff_colorable.mp h2
  rcases hc with ⟨c⟩
  have h_col : is_valid_coloring (c (moser_points 0)) (c (moser_points 1)) (c (moser_points 2)) (c (moser_points 3)) (c (moser_points 4)) (c (moser_points 5)) (c (moser_points 6)) = true := by
    simp [is_valid_coloring, c.map_rel, edge01, edge02, edge12, edge13, edge23, edge04, edge05, edge45, edge46, edge56, edge36]
  have h_no := no_3_coloring (c (moser_points 0)) (c (moser_points 1)) (c (moser_points 2)) (c (moser_points 3)) (c (moser_points 4)) (c (moser_points 5)) (c (moser_points 6))
  rw [h_col] at h_no
  contradiction

/--
This upper bound for the chromatic number of the plane was
observed by John R. Isbell. His approach was dividing the
plane into hexagons of uniform size and coloring them with a repeating
pattern. A proof can probably be found in:

Soifer, Alexander (2008), The Mathematical Coloring Book: Mathematics of Coloring and the Colorful Life of its Creators, New York: Springer, ISBN 978-0-387-74640-1

An alternative approach that uses square tiling was highlighted by László Székely.
-/
@[category high_school, AMS 52]
theorem HadwigerNelsonAtMostSeven :
    χ(ℝ²) ≤ 7 := by
  sorry

/-- The chromatic number of the plane is at least 3.

This is proven by considering an equilateral triangle in the plane. -/
@[category high_school, AMS 5]
theorem HadwigerNelsonAtLeastThree : 3 ≤ χ(ℝ²) :=
  le_chromaticNumber_of_pairwise_adj (by simp) ![!₂[0, 0], !₂[1, 0], !₂[0.5, Real.sqrt 3 / 2]] <| by
    simp [pairwise_fin_succ_iff_of_isSymm, Fin.forall_fin_succ]
    simp [UnitDistancePlaneGraph, PiLp.dist_eq_of_L2, Real.dist_eq, div_pow]
    norm_num

end Erdos508
