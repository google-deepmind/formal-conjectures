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

public import FormalConjecturesForMathlib.Computability.LabelCover
public import FormalConjecturesForMathlib.Computability.PromiseGraph
public import FormalConjecturesForMathlib.Computability.SmallSetExpansion
public import FormalConjecturesForMathlib.Computability.GapSatisfiability
public meta import FormalConjecturesForMathlib.Computability.LabelCover
public meta import FormalConjecturesForMathlib.Computability.GapSatisfiability

/-!
# Approximation and promise-problem boundary tests

No research statement is imported. Finite examples are kernel checked.
-/

@[expose] public section

namespace PromiseApproximationTest

open Computability ComplexityTheory

example : PromiseReduction (fun x : Bool => x = true) (fun x => x = false)
    (fun x => x = true) (fun x => x = false) := PromiseReduction.refl _ _

theorem overlapping_regions_not_hard :
    ¬ PromiseNPHard (fun _ : Bool => True) (fun _ => True) := by
  intro h
  exact h.1 false trivial trivial

theorem overlapping_regions_no_separator :
    ¬ HasPolyTimeSeparator (fun _ : Bool => True) (fun _ => True) := by
  intro h
  exact h.disjoint false trivial trivial

theorem identity_separator :
    HasPolyTimeSeparator (fun x : Bool => x = true) (fun x => x = false) :=
  ⟨id, isPolyTime_id, fun _ hx => hx, fun _ hx => hx⟩

example (yes no : Bool → Prop) (s t : Bool → ℕ) (h : HasTimeSeparator yes no s)
    (hst : ∀ x, s x ≤ t x) : HasTimeSeparator yes no t := h.mono hst

section LabelCover

open LabelCover

example : Projection 1 2 [0, 1] := by decide +kernel
example : Projection 1 2 [1, 0] := by decide +kernel
example : ¬ Projection 1 2 [0, 0] := by decide +kernel
example : Projection 2 2 [0, 0] := by decide +kernel
example : ¬ Projection 2 2 [0] := by decide +kernel
example : ¬ Projection 2 2 [0, 2] := by decide +kernel
example : ¬ Projection 2 3 [0, 0, 0] := by decide +kernel
example : ¬ Valid 1 0 [(0, 0, [])] := by decide +kernel
example : ¬ Valid 1 1 [] := by decide +kernel
example : Valid 1 1 [(0, 0, [0])] := by decide +kernel
example : Yes 1 1 1 [(0, 0, [0])] := by decide +kernel
example : ¬ No 1 1 (1 / 2) [(0, 0, [0])] := by decide +kernel
example : ¬ Valid 1 1 [(0, 1, [0])] := by decide +kernel
example : ¬ Valid 1 1 [(0, 0, [0]), (0, 0, [0])] := by decide +kernel

/-- Two distinct edges force opposite labels at the same right vertex. -/
def conflictingStar : Code := [(0, 0, [0, 0]), (1, 0, [1, 1])]

example : Valid 2 2 conflictingStar := by decide +kernel
example : ¬ Valid 1 2 conflictingStar := by decide +kernel
example : AtLeast 2 (1 / 2) conflictingStar := by decide +kernel
example : AtMost 2 (1 / 2) conflictingStar := by decide +kernel
example : No 2 2 (1 / 2) conflictingStar := by decide +kernel
example : ¬ Yes 2 2 1 conflictingStar := by decide +kernel
example : ¬ Yes 2 2 (3 / 4) conflictingStar := by decide +kernel
example : ¬ No 2 2 (1 / 4) conflictingStar := by decide +kernel

/-- An inconsistent parity cycle is nearly, but not perfectly, satisfiable. -/
def parityCycle : Code :=
  [(0, 0, [0, 1]), (0, 1, [0, 1]), (1, 0, [0, 1]), (1, 1, [1, 0])]

example : Valid 1 2 parityCycle := by decide +kernel
example : AtLeast 2 (3 / 4) parityCycle := by decide +kernel
example : AtMost 2 (3 / 4) parityCycle := by decide +kernel
example : ¬ AtLeast 2 1 parityCycle := by decide +kernel

example {d q : ℕ} {c s : ℚ} {g : Code} (hsc : s < c) (hy : Yes d q c g) :
    ¬ No d q s g := yes_not_no hsc hy

end LabelCover

/-- An edge, a triangle, a complete graph on four vertices, and two disjoint edges. -/
abbrev k2 : MatrixGraph.Code := [[false, true], [true, false]]

abbrev k3 : MatrixGraph.Code :=
  [[false, true, true], [true, false, true], [true, true, false]]

abbrev k4 : MatrixGraph.Code :=
  [[false, true, true, true], [true, false, true, true],
   [true, true, false, true], [true, true, true, false]]

abbrev twoEdges : MatrixGraph.Code :=
  [[false, true, false, false], [true, false, false, false],
   [false, false, false, true], [false, false, true, false]]

section PromiseGraph

open PromiseGraph

example : MatrixGraph.ValidGraph k3 := by decide +kernel
example : Nonbipartite k3 := by decide +kernel
example : ¬ Nonbipartite k2 := by decide +kernel

example {g h : MatrixGraph.Code} (hgh : Hom g h) (hg : Nonbipartite g) :
    Nonbipartite h := hgh.nonbipartite hg
example : Hom k3 k4 := by decide +kernel
example : ¬ Hom k3 k2 := by decide +kernel
example : Yes k3 k3 := ⟨by simp [MatrixGraph.Square, k3], Hom.refl _⟩
example : No k3 k4 := by decide +kernel
example : ¬ Yes k3 k4 := by decide +kernel
example : ¬ No k4 k4 := by decide +kernel
example : Hom [] [] := by decide +kernel
example : Hom [] k3 := by decide +kernel
example : ¬ Hom k3 [] := by decide +kernel
example : Yes k3 [] := by decide +kernel
example : ¬ No k3 [] := by decide +kernel
example : No k3 [[true]] := by decide +kernel
example : ¬ Yes k3 [[true]] := by decide +kernel
example : Yes k3 [[false, true], [false, false]] := by decide +kernel
example : ¬ Yes k3 [[false, true]] := by decide +kernel
example : ¬ No k3 [[false, true]] := by decide +kernel

example {g h x : MatrixGraph.Code} (hgh : Hom g h) (hy : Yes g x) :
    ¬ No h x := yes_not_no hgh hy

end PromiseGraph

section SmallSetExpansion

open SmallSetExpansion

example : degree k2 0 = 1 := by decide +kernel
example : boundary k2 {0} = 1 := by decide +kernel
example : boundary k2 {0, 1} = 0 := by decide +kernel
example : boundary twoEdges {0, 1} = 0 := by decide +kernel
example : boundary twoEdges {0, 2} = 2 := by decide +kernel
example : HasSize (1 / 2) k2 {0} := by decide +kernel
example : ¬ HasSize (1 / 3) k2 {0} := by decide +kernel
example : ¬ HasSize 0 k2 {} := by decide +kernel
example : Valid (1 / 2) (k2, 1) := by decide +kernel
example : ¬ Valid (1 / 3) (k2, 1) := by decide +kernel
example : ¬ Valid (1 / 2) (k2, 0) := by decide +kernel
example : ¬ Valid (1 / 2) (k2, 2) := by decide +kernel
example : ¬ Valid (1 / 2) ([], 1) := by decide +kernel
example : ¬ Valid 1 ([[true]], 1) := by decide +kernel
example : ¬ Valid 1 ([[false]], 0) := by decide +kernel
example : ¬ Valid (1 / 3)
    ([[false, true, false], [true, false, true], [false, true, false]], 1) := by decide +kernel
example : No (1 / 10) (1 / 2) (k2, 1) := by decide +kernel
example : ¬ Yes (1 / 10) (1 / 2) (k2, 1) := by decide +kernel
example : Yes 0 (1 / 2) (twoEdges, 1) := by decide +kernel
example : ¬ No (1 / 10) (1 / 2) (twoEdges, 1) := by decide +kernel

example {η δ : ℚ} {x : Input} (hη : η < 1 / 2) (hy : Yes η δ x) :
    ¬ No η δ x := yes_not_no hη hy

end SmallSetExpansion

section GapSatisfiability

open GapSatisfiability BooleanSatisfiability

example : ¬ Valid [] := by decide +kernel
example : ¬ Yes [] := by decide +kernel
example : ¬ No (1 / 2) [] := by decide +kernel
example : Valid [[]] := by decide +kernel
example : No (1 / 2) [[]] := by decide +kernel
example : ¬ Yes [[]] := by decide +kernel
example : Yes [[(0, true)]] := by decide +kernel
example : ¬ No (1 / 2) [[(0, true)]] := by decide +kernel
example : Yes [[(0, true), (0, false)]] := by decide +kernel
example : No (1 / 2) [[(0, true)], [(0, false)]] := by decide +kernel
example : ¬ No (3 / 4) [[(0, true)], [(0, false)]] := by decide +kernel
example : ¬ Valid [[(0, true), (1, true), (2, true), (3, true)]] := by decide +kernel
example : satisfied [[(0, true)], [(0, true)], [(0, false)]] {0} = 2 := by decide +kernel
example : No (1 / 3) [[(0, true)], [(0, true)], [(0, false)]] := by decide +kernel
example : ¬ No (1 / 2) [[(0, true)], [(0, true)], [(0, false)]] := by decide +kernel
example : (support [[(1000000, true), (1000000, false)]]).card = 1 := by decide +kernel
example : (support [[(7, true)], [(42, true)]]).card = 2 := by decide +kernel

example {ε : ℚ} (hε : 0 < ε) {formula : Formula} (hy : Yes formula) :
    ¬ No ε formula := yes_not_no hε hy

end GapSatisfiability

#guard decide (LabelCover.No 2 2 (1 / 2) conflictingStar)
#guard !decide (LabelCover.Yes 2 2 1 conflictingStar)
#guard GapSatisfiability.satisfied [[(0, true)], [(0, true)], [(0, false)]] {0} == 2

end PromiseApproximationTest
