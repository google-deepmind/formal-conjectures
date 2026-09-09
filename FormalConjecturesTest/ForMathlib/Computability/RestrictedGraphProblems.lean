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

public meta import FormalConjecturesForMathlib.Computability.RestrictedGraphProblems
public import FormalConjecturesForMathlib.Computability.RestrictedGraphProblems
public import FormalConjecturesForMathlib.Computability.DecisionProblems

/-! # Degree boundaries, vertex/edge colors, and monochromatic matching tests -/

@[expose] public section

namespace Computability.MatrixGraph.RestrictedTest

open BitstringEncoding ComplexityTheory

def isolated : Code :=
  [[false]]

def edge : Code :=
  [[false, true],
    [true, false]]

def triangle : Code :=
  [[false, true, true],
    [true, false, true],
    [true, true, false]]

def completeFour : Code :=
  [[false, true, true, true],
    [true, false, true, true],
    [true, true, false, true],
    [true, true, true, false]]

def cycleFour : Code :=
  [[false, true, false, true],
    [true, false, true, false],
    [false, true, false, true],
    [true, false, true, false]]

def starFour : Code :=
  [[false, true, true, true, true],
    [true, false, false, false, false],
    [true, false, false, false, false],
    [true, false, false, false, false],
    [true, false, false, false, false]]

def starFive : Code :=
  [[false, true, true, true, true, true],
    [true, false, false, false, false, false],
    [true, false, false, false, false, false],
    [true, false, false, false, false, false],
    [true, false, false, false, false, false],
    [true, false, false, false, false, false]]

def bipartiteThree : Code :=
  [[false, false, false, true, true, true],
    [false, false, false, true, true, true],
    [false, false, false, true, true, true],
    [true, true, true, false, false, false],
    [true, true, true, false, false, false],
    [true, true, true, false, false, false]]

def prism : Code :=
  [[false, true, true, true, false, false],
    [true, false, true, false, true, false],
    [true, true, false, false, false, true],
    [true, false, false, false, true, true],
    [false, true, false, true, false, true],
    [false, false, true, true, true, false]]

def fourWithIsolate : Code :=
  [[false, true, true, true, false],
    [true, false, true, true, false],
    [true, true, false, true, false],
    [true, true, true, false, false],
    [false, false, false, false, false]]

example : DegreeAtMost [] 0 := by decide
example : DegreeAtMost isolated 0 := by decide
example : ¬ DegreeAtMost edge 0 := by decide
example : DegreeAtMost edge 1 := by decide
example : DegreeAtMost triangle 2 := by decide
example : ¬ DegreeAtMost triangle 1 := by decide
example : DegreeAtMost completeFour 3 := by decide
example : ¬ DegreeAtMost completeFour 2 := by decide
example : DegreeAtMost starFour 4 := by decide
example : ¬ DegreeAtMost starFour 3 := by decide
example : DegreeAtMost starFive 5 := by decide
example : ¬ DegreeAtMost starFive 4 := by decide

example : CubicGraph [] := by decide
example : ¬ CubicGraph isolated := by decide
example : ¬ CubicGraph edge := by decide
example : ¬ CubicGraph triangle := by decide
example : CubicGraph completeFour := by decide
example : CubicGraph bipartiteThree := by decide
example : CubicGraph prism := by decide
example : ¬ CubicGraph cycleFour := by decide
example : ¬ CubicGraph fourWithIsolate := by decide
example : ¬ CubicGraph [[true]] := by decide
example : ¬ CubicGraph [[false, true], [false, false]] := by decide
example : ¬ CubicGraph [[false], [false, false]] := by decide

example : DegreeFourThreeColorable [] := by decide
example : DegreeFourThreeColorable isolated := by decide
example : DegreeFourThreeColorable triangle := by decide
example : ¬ DegreeFourThreeColorable completeFour := by decide
example : DegreeFourThreeColorable cycleFour := by decide
example : DegreeFourThreeColorable starFour := by decide
set_option maxRecDepth 2048 in
example : Colorable (starFive, 3) := by decide
example : ¬ DegreeFourThreeColorable starFive := by decide
example : DegreeFourThreeColorable bipartiteThree := by decide
set_option maxRecDepth 2048 in
example : DegreeFourThreeColorable prism := by decide
example : ¬ DegreeFourThreeColorable [[true]] := by decide
example : ¬ DegreeFourThreeColorable [[false, true], [false, false]] := by decide
example : ¬ DegreeFourThreeColorable [[false], [false, false]] := by decide

example : SubcubicVertexCover ([], 1) := by decide
example : ¬ SubcubicVertexCover ([], 0) := by decide
example : SubcubicVertexCover (isolated, 1) := by decide
example : SubcubicVertexCover (edge, 1) := by decide
example : ¬ SubcubicVertexCover (edge, 0) := by decide
example : ¬ SubcubicVertexCover (triangle, 1) := by decide
example : SubcubicVertexCover (triangle, 2) := by decide
example : ¬ SubcubicVertexCover (completeFour, 2) := by decide
example : SubcubicVertexCover (completeFour, 3) := by decide
example : ¬ SubcubicVertexCover (cycleFour, 1) := by decide
example : SubcubicVertexCover (cycleFour, 2) := by decide
example : ¬ SubcubicVertexCover (bipartiteThree, 2) := by decide
example : SubcubicVertexCover (bipartiteThree, 3) := by decide
example : VertexCover (starFour, 1) := by decide
example : ¬ SubcubicVertexCover (starFour, 1) := by decide
example : ¬ SubcubicVertexCover ([[true]], 1) := by decide
example : ¬ SubcubicVertexCover ([[false, true], [false, false]], 1) := by decide

example : CubicEdgeThreeColorable [] := by decide
example : ¬ CubicEdgeThreeColorable isolated := by decide
example : ¬ CubicEdgeThreeColorable triangle := by decide
/-- The three pairs of opposite edges of K4 receive different labels. -/
def completeFourLabels : (toGraph completeFour).EdgeLabeling (Fin 3) :=
  .mk (fun v w _ ↦ if v.val + w.val = 3 then 0 else if (v.val + w.val) % 2 = 0 then 1 else 2)
    (by intros; simp only [Nat.add_comm])

theorem completeFour_edgeColorable : CubicEdgeThreeColorable completeFour :=
  ⟨by decide, completeFourLabels, by decide⟩
example : ¬ CubicEdgeThreeColorable fourWithIsolate := by decide
example : ¬ CubicEdgeThreeColorable [[true]] := by decide
example : ¬ CubicEdgeThreeColorable [[false, true], [false, false]] := by decide

/-- A fixed constant labeling fails properness on incident edges. -/
def constantLabels : (toGraph completeFour).EdgeLabeling (Fin 3) := fun _ ↦ 0

example : ¬ constantLabels.IsProper := by decide
theorem triangle_not_edgeTwoColorable :
    ¬ ∃ c : (toGraph triangle).EdgeLabeling (Fin 2), c.IsProper := by
  rintro ⟨c, hc⟩
  have h := c.isProper_iff.mp hc
  let v0 : Fin triangle.length := ⟨0, by decide⟩
  let v1 : Fin triangle.length := ⟨1, by decide⟩
  let v2 : Fin triangle.length := ⟨2, by decide⟩
  have h0 := h v0 v1 v2 (by decide) (by decide) (by decide)
  have h1 := h v1 v0 v2 (by decide) (by decide) (by decide)
  have h2 := h v2 v0 v1 (by decide) (by decide) (by decide)
  rw [c.get_comm v0 v1] at h1
  rw [c.get_comm v0 v2, c.get_comm v1 v2] at h2
  omega

/-- Three distinct labels on the three edges of a triangle. -/
def triangleLabels : (toGraph triangle).EdgeLabeling (Fin 3) :=
  .mk (fun v w _ ↦ ⟨(v.val + w.val) % 3, Nat.mod_lt _ (by decide)⟩)
    (by intros; simp only [Nat.add_comm])

theorem triangle_edgeThreeColorable :
    ∃ c : (toGraph triangle).EdgeLabeling (Fin 3), c.IsProper :=
  ⟨triangleLabels, by decide⟩
example (c : (toGraph completeFour).EdgeLabeling (Fin 3)) :
    c.get ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide) =
      c.get ⟨1, by decide⟩ ⟨0, by decide⟩ (by decide) :=
  c.get_comm _ _ _

example : ¬ CubicHamiltonian [] := by decide
example : ¬ CubicHamiltonian isolated := by decide
example : UndirectedHamiltonian triangle := by decide
example : ¬ CubicHamiltonian triangle := by decide
example : CubicHamiltonian completeFour := by decide
example : CubicHamiltonian bipartiteThree := by decide
example : CubicHamiltonian prism := by decide
example : ¬ CubicHamiltonian fourWithIsolate := by decide
example : ¬ CubicHamiltonian [[true]] := by decide

example : SameColorMatching [] (fun _ ↦ false) := by decide
example : ¬ SameColorMatching isolated (fun _ ↦ false) := by decide
example : SameColorMatching edge (fun _ ↦ false) := by decide
example : ¬ SameColorMatching edge (fun v ↦ decide (v.val = 0)) := by decide
example : ¬ SameColorMatching triangle (fun _ ↦ false) := by decide
example : ¬ SameColorMatching completeFour (fun _ ↦ false) := by decide
example : SameColorMatching completeFour (fun v ↦ decide (v.val < 2)) := by decide
example : SameColorMatching completeFour (fun v ↦ !(decide (v.val < 2))) := by decide
example : (sameColorSubgraph completeFour (fun v ↦ decide (v.val < 2))).IsPerfectMatching :=
  (sameColorMatching_iff _ _).mp (by decide)

example : CubicTwoColorMatching [] := by decide
example : ¬ CubicTwoColorMatching isolated := by decide
example : ¬ CubicTwoColorMatching edge := by decide
example : CubicTwoColorMatching completeFour := by decide
-- K3,3 is properly 2-colorable, but has no coloring with one same-color neighbor per vertex.
example : Colorable (bipartiteThree, 2) := by decide
example : ¬ CubicTwoColorMatching bipartiteThree := by decide
example : ¬ CubicTwoColorMatching fourWithIsolate := by decide
example : ¬ CubicTwoColorMatching [[true]] := by decide
example : ¬ CubicTwoColorMatching [[false, true], [false, false]] := by decide

example (a : Code) : bitDecode (bitEncode a) = some a := by simp
example (input : Code × ℕ) : bitDecode (bitEncode input) = some input := by simp
example : (bitEncode completeFour).length = 100 := by decide
set_option maxRecDepth 2048 in
example : (bitEncode bipartiteThree).length = 222 := by decide

/-- A real polynomial-time machine witnesses that the decider interface is nonvacuous. -/
theorem nonvacuous_machine_interface : HasPolyTimeDecider (fun b : Bool ↦ b = true) :=
  isPolyTime_id.hasPolyTimeDecider

/-- info: (true, false, true) -/
#guard_msgs in
#eval (decide (DegreeFourThreeColorable starFour),
  decide (SubcubicVertexCover (starFour, 1)), decide (CubicEdgeThreeColorable completeFour))

/-- info: (true, true, false) -/
#guard_msgs in
#eval (decide (CubicHamiltonian bipartiteThree),
  decide (CubicTwoColorMatching completeFour), decide (CubicTwoColorMatching bipartiteThree))

end Computability.MatrixGraph.RestrictedTest
