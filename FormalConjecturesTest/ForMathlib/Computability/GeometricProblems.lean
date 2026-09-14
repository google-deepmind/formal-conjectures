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
import FormalConjecturesForMathlib.Computability.DecisionProblems
import FormalConjecturesForMathlib.Computability.GeometricProblems
import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Tactic.NormNum.RealSqrt

/-!
# Geometry boundary and semantic tests

Kernel proofs check exact lengths, affine-line incidence, true graph trees,
closed disk boundaries, and rational encodings. Guarded runtime checks cover
only the explicitly executable unit-disk predicates.
-/

namespace Computability.GeometricProblems.Test

-- Exact Euclidean, not Manhattan or product sup distance.
example : squaredDistance (0, 0) (3, 4) = 25 := by decide +kernel
example : squaredDistance (-1, 2) (2, -2) = 25 := by decide +kernel
example : squaredDistance (0, 0) (3/5, 4/5) = 1 := by decide +kernel
example : euclideanLength (0, 0) (3, 4) = 5 := by
  norm_num [euclideanLength, dist_toEuclidean, rationalPoint, squaredDistance]
example : euclideanLength (0, 0) (1, 1) = Real.sqrt 2 := by
  norm_num [euclideanLength, dist_toEuclidean, rationalPoint, squaredDistance]
example : rectilinearLength (0, 0) (3, 4) = 7 := by decide +kernel
example : rectilinearLength (-2, 3) (1, -1) = 7 := by decide +kernel

-- Empty, singleton, malformed, and zero-budget TSP inputs.
example : EuclideanTravelingSalesman ([], 1) := by
  refine ⟨by simp, by decide +kernel, Equiv.refl _, ?_⟩
  simp [tourLength]
example : EuclideanTravelingSalesman ([(7, -9)], 1) := by
  refine ⟨by simp, by decide +kernel, Equiv.refl _, ?_⟩
  simp [tourLength, next, euclideanLength]
example : ¬ EuclideanTravelingSalesman ([], 0) := by
  simp [EuclideanTravelingSalesman]
example : ¬ EuclideanTravelingSalesman ([(0, 0), (0, 0)], 10) := by
  simp [EuclideanTravelingSalesman]

theorem pair_tour (p q : IntegerPoint) (order : Equiv.Perm (Fin 2)) :
    tourLength [p, q] order = 2 * euclideanLength p q := by
  have hne : order 0 ≠ order 1 := order.injective.ne (by decide +kernel)
  have h0 := (order 0).isLt
  have h1 := (order 1).isLt
  have hcases : (order 0 = 0 ∧ order 1 = 1) ∨
      (order 0 = 1 ∧ order 1 = 0) := by omega
  have hs : euclideanLength q p = euclideanLength p q := dist_comm _ _
  rcases hcases with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
    simp [tourLength, Fin.sum_univ_two, next, ha, hb, hs, two_mul]

example : EuclideanTravelingSalesman ([(0, 0), (3, 4)], 10) := by
  refine ⟨by decide +kernel, by decide +kernel, Equiv.refl _, ?_⟩
  rw [pair_tour]
  norm_num [euclideanLength, dist_toEuclidean, rationalPoint, squaredDistance]
example : ¬ EuclideanTravelingSalesman ([(0, 0), (3, 4)], 9) := by
  rintro ⟨_, _, order, h⟩
  rw [pair_tour] at h
  norm_num [euclideanLength, dist_toEuclidean, rationalPoint, squaredDistance] at h
example : EuclideanTravelingSalesman ([(0, 0), (1, 1)], 3) := by
  refine ⟨by decide +kernel, by decide +kernel, Equiv.refl _, ?_⟩
  rw [pair_tour]
  norm_num [euclideanLength, dist_toEuclidean, rationalPoint, squaredDistance]
  have h := (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 3/2)).mpr
    (by norm_num : (2 : ℝ) ≤ (3/2)^2)
  linarith

-- Unrestricted geometric Steiner vertices; an empty terminal set permits a singleton.
theorem singleton_tree_length (p : IntegerPoint) :
    rectilinearTreeLength (⊥ : SimpleGraph ({p} : Finset IntegerPoint)) = 0 := by
  classical
  simp [rectilinearTreeLength]

example : RectilinearSteinerTree ([], 1) := by
  refine ⟨by simp, by decide +kernel, {(0, 0)}, by simp, ⊥, ?_, ?_⟩
  · exact SimpleGraph.IsTree.of_subsingleton
  · rw [singleton_tree_length]
    decide
example : RectilinearSteinerTree ([(5, -2)], 1) := by
  refine ⟨by simp, by decide +kernel, {(5, -2)}, by simp, ⊥, ?_, ?_⟩
  · exact SimpleGraph.IsTree.of_subsingleton
  · rw [singleton_tree_length]
    decide
example : ¬ RectilinearSteinerTree ([], 0) := by simp [RectilinearSteinerTree]
example : ¬ RectilinearSteinerTree ([(0, 0), (0, 0)], 2) := by
  simp [RectilinearSteinerTree]

def steinerPoints : Finset IntegerPoint := {(0, 0), (2, 0), (1, 1), (1, 0)}
def steinerCenter : steinerPoints := ⟨(1, 0), by decide +kernel⟩

-- A new Steiner point joins three terminals with total length three.
-- Connecting only the three terminals would require total length four.
example : RectilinearSteinerTree ([(0, 0), (2, 0), (1, 1)], 3) := by
  classical
  let G := SimpleGraph.starGraph steinerCenter
  have ht : G.IsTree := SimpleGraph.isTree_starGraph _
  refine ⟨by decide +kernel, by decide +kernel, steinerPoints, by decide +kernel, G, ht, ?_⟩
  have hunit : ∀ a b : steinerPoints, G.Adj a b → rectilinearLength a.val b.val ≤ 1 := by
    decide
  have he (e : Sym2 steinerPoints) (h : e ∈ G.edgeFinset) :
      rectilinearEdgeLength e ≤ 1 := by
    induction e using Sym2.inductionOn with
    | _ a b =>
      exact hunit a b (SimpleGraph.mem_edgeFinset.mp h)
  have hc : G.edgeFinset.card = 3 := by
    have h := ht.card_edgeFinset
    have hs : Fintype.card steinerPoints = 4 := by decide +kernel
    omega
  calc
    rectilinearTreeLength G ≤ ∑ e ∈ G.edgeFinset, 1 := by
      rw [rectilinearTreeLength_eq]
      exact Finset.sum_le_sum he
    _ = 3 := by simp [hc]

-- Arbitrary affine lines, including vertical and oblique ones.
example : (Line.vertical 2).Contains (2, 7) := by norm_num [Line.vertical, Line.Contains]
example : ¬ (Line.vertical 2).Contains (3, 7) := by
  norm_num [Line.vertical, Line.Contains]
example : LineCover ([], 0) := by simp
example : ¬ LineCover ([(0, 0)], 0) := by simp
example : ¬ LineCover ([(0, 0), (0, 0)], 2) := by simp [LineCover]
example : LineCover ([(1/2, -7), (1/2, 4)], 1) := by
  refine ⟨by decide +kernel, fun _ ↦ Line.vertical (1/2), ?_⟩
  norm_num [Line.vertical, Line.Contains]
example : LineCover ([(0, 0), (1, 1), (2, 2)], 1) := by
  refine ⟨by decide +kernel, fun _ ↦ ⟨1, -1, 0, Or.inl one_ne_zero⟩, ?_⟩
  norm_num [Line.Contains]
example : ¬ LineCover ([(0, 0), (1, 0), (0, 1)], 1) := by
  rintro ⟨_, lines, h⟩
  have h0 := h (0, 0) (by simp)
  have h1 := h (1, 0) (by simp)
  have h2 := h (0, 1) (by simp)
  simp only [Fin.exists_fin_one, Line.Contains] at h0 h1 h2
  norm_num at h0 h1 h2
  rcases (lines 0).normal_ne_zero with ha | hb
  · exact ha (h1.trans h0.symm)
  · exact hb (h2.trans h0.symm)
example : LineCover ([(0, 0), (1, 0), (0, 1)], 2) := by
  refine ⟨by decide +kernel, fun i ↦ Line.horizontal i.val, ?_⟩
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨0, by norm_num [Line.horizontal, Line.Contains]⟩
  · exact ⟨0, by norm_num [Line.horizontal, Line.Contains]⟩
  · exact ⟨1, by norm_num [Line.horizontal, Line.Contains]⟩

-- Unit disks: tangency is an edge, and domination includes self-coverage.
example : (unitDiskGraph [(0, 0), (3/5, 4/5)] 1).Adj 0 1 := by decide +kernel
example : ¬ (unitDiskGraph [(0, 0), (3/5, 4/5)] 1).Adj 0 0 := by decide +kernel
example : ¬ UnitDiskIndependentSet ([(0, 0), (3/5, 4/5)], 1, 2) := by decide +kernel
example : UnitDiskIndependentSet ([(0, 0), (3/5, 4/5)], 1, 1) := by decide +kernel
example : UnitDiskIndependentSet ([(0, 0), (1, 1)], 1, 2) := by decide +kernel
example : UnitDiskDominatingSet ([(0, 0), (3/5, 4/5)], 1, 1) := by decide +kernel
example : ¬ UnitDiskDominatingSet ([(0, 0), (1, 1)], 1, 1) := by decide +kernel
example : UnitDiskDominatingSet ([(0, 0), (1, 1)], 1, 2) := by decide +kernel
example : UnitDiskDominatingSet ([(0, 0)], 1, 1) := by decide +kernel
example : ¬ UnitDiskDominatingSet ([(0, 0)], 1, 0) := by decide +kernel
example : UnitDiskIndependentSet ([], 1, 0) := by decide +kernel
example : ¬ UnitDiskIndependentSet ([], 1, 1) := by decide +kernel
example : UnitDiskDominatingSet ([], 1, 0) := by decide +kernel
example : ¬ UnitDiskIndependentSet ([], 0, 0) := by decide +kernel
example : ¬ UnitDiskDominatingSet ([], -1, 0) := by decide +kernel
example : ¬ UnitDiskIndependentSet ([(0, 0), (0, 0)], 1, 1) := by decide +kernel
example : ¬ UnitDiskDominatingSet ([(0, 0), (0, 0)], 1, 1) := by decide +kernel
example : UnitDiskDominatingSet ([(-1, 0), (0, 0), (1, 0)], 1, 1) := by decide +kernel
example : UnitDiskIndependentSet ([(-1, 0), (0, 0), (1, 0)], 1, 2) := by decide +kernel
example : UnitDiskIndependentSet ([(0, 0), (3/5, 4/5)], 1/2, 2) := by decide +kernel

-- A rationally represented odd cycle: this is not the bipartite integer-grid subclass.
def pentagon : List Point := [(0, 4/5), (4/5, 1/5), (1/2, -3/5),
  (-1/2, -3/5), (-4/5, 1/5)]
example : UnitDiskIndependentSet (pentagon, 1, 2) := by decide +kernel
example : ¬ UnitDiskIndependentSet (pentagon, 1, 3) := by decide +kernel
example : UnitDiskDominatingSet (pentagon, 1, 2) := by decide +kernel
example : ¬ UnitDiskDominatingSet (pentagon, 1, 1) := by decide +kernel

-- Binary rational and composite input round trips.
example (x : UnitDiskInput) :
    BitstringEncoding.bitDecode (BitstringEncoding.bitEncode x) = some x := by simp
example (x : List IntegerPoint × ℕ) :
    BitstringEncoding.bitDecode (BitstringEncoding.bitEncode x) = some x := by simp
example (x : List Point × ℕ) :
    BitstringEncoding.bitDecode (BitstringEncoding.bitEncode x) = some x := by simp
example : BitstringEncoding.bitDecode
    (BitstringEncoding.bitEncode ((-3/7, 100/13) : Point)) =
      some ((-3/7, 100/13) : Point) := by decide +kernel

example : ComplexityTheory.HasPolyTimeDecider (fun b : Bool ↦ b = true) :=
  ComplexityTheory.isPolyTime_id.hasPolyTimeDecider

#guard decide (UnitDiskIndependentSet ([(0, 0), (1, 1)], 1, 2))
#guard !decide (UnitDiskDominatingSet ([(0, 0), (1, 1)], 1, 1))

end Computability.GeometricProblems.Test
