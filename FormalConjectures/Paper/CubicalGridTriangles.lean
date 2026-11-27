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

public import FormalConjecturesUtil

/-!
# A limit for the number of triangle shapes in a cubical grid

Let $a(n)$ count congruence classes of nondegenerate triangles with vertices in
$\{0,\ldots,n\}^3$. Congruence is ordinary Euclidean congruence. Huber proves that
$a(n)=\Theta(n^6/\sqrt{\log n})$ and asks whether the normalized count has a limit.

The finite encoding below is the paper's exact formula: each coordinate contributes a
triple of squared lengths, and three such contributions are added. Sorting identifies
triangles with the same side lengths, and a strict Heron-polynomial inequality removes
degenerate triangles.

*References:*
* F. Huber,
  [Congruence Classes of Triangles in a Cubical Grid](https://zenodo.org/records/23158188),
  version 2.0, October 5, 2026, exact encoding theorem and Perspective section.
* [OEIS A400001](https://oeis.org/A400001), formerly A400663.
-/

@[expose] public section

namespace CubicalGridTriangles

open Filter
open scoped Topology

/-- A triple of squared side lengths, with integer arithmetic for the Heron polynomial. -/
abbrev SquaredLengths := ℤ × ℤ × ℤ

/-- Distinct contributions of one coordinate to the three squared side lengths. -/
def coordinateContributions (n : ℕ) : List SquaredLengths :=
  ((List.range (n + 1)).flatMap fun a =>
    (List.range (n + 1)).flatMap fun b =>
      (List.range (n + 1)).map fun c =>
        (((b : ℤ) - a) ^ 2, ((c : ℤ) - a) ^ 2, ((b : ℤ) - c) ^ 2)).dedup

/-- Sixteen times the squared area, expressed in squared side lengths. -/
def heronPolynomial (t : SquaredLengths) : ℤ :=
  2 * (t.1 * t.2.1 + t.1 * t.2.2 + t.2.1 * t.2.2) -
    t.1 ^ 2 - t.2.1 ^ 2 - t.2.2 ^ 2

/-- A congruence class is recorded by its three squared side lengths in increasing order. -/
def sortedLengths (t : SquaredLengths) : List ℤ :=
  let lo := min t.1 t.2.1
  let hi := max t.1 t.2.1
  [min lo t.2.2, max lo (min hi t.2.2), max hi t.2.2]

/-- Pair sums with repetition, listing each unordered choice of positions once. -/
def pairSums : List SquaredLengths → List SquaredLengths
  | [] => []
  | x :: xs => ((x :: xs).map fun y => x + y) ++ pairSums xs

/-- Triple sums with repetition, listing each unordered choice of positions once. -/
def tripleSums : List SquaredLengths → List SquaredLengths
  | [] => []
  | x :: xs => ((pairSums (x :: xs)).map fun y => x + y) ++ tripleSums xs

/-- The squared-length triples of nondegenerate triangle shapes in the cubical grid. -/
def triangleClasses (n : ℕ) : Finset (List ℤ) :=
  (((tripleSums (coordinateContributions n)).filter fun t =>
      0 < heronPolynomial t).map sortedLengths).toFinset

/-- The number of congruence classes, with the official index starting at zero. -/
def a (n : ℕ) : ℕ := (triangleClasses n).card

@[category test, AMS 5 11 51]
theorem a_0 : a 0 = 0 := by
  unfold a triangleClasses
  rw [List.card_to_finset_eq_tree_set_size _ compare]
  decide +kernel

@[category test, AMS 5 11 51]
theorem a_1 : a 1 = 3 := by
  unfold a triangleClasses
  rw [List.card_to_finset_eq_tree_set_size _ compare]
  decide +kernel

@[category test, AMS 5 11 51]
theorem a_2 : a 2 = 40 := by
  unfold a triangleClasses
  rw [List.card_to_finset_eq_tree_set_size _ compare]
  decide +kernel

set_option maxRecDepth 10000 in
@[category test, AMS 5 11 51]
theorem a_3 : a 3 = 214 := by
  have hc : coordinateContributions 3 =
      [(4, 1, 9), (1, 4, 9), (1, 1, 4), (9, 9, 0),
       (9, 4, 1), (9, 1, 4), (9, 0, 9), (4, 9, 1),
       (4, 4, 0), (4, 1, 1), (4, 0, 4), (1, 9, 4),
       (1, 4, 1), (1, 1, 0), (1, 0, 1), (0, 9, 9),
       (0, 4, 4), (0, 1, 1), (0, 0, 0)] := by decide +kernel
  unfold a triangleClasses
  rw [hc, List.card_to_finset_eq_tree_set_size _ compare]
  decide +kernel

set_option maxRecDepth 20000 in
@[category test, AMS 5 11 51]
theorem a_4 : a 4 = 830 := by
  have hc : coordinateContributions 4 =
      [(4, 4, 16), (9, 1, 16), (4, 1, 9), (1, 9, 16),
       (1, 4, 9), (1, 1, 4), (16, 16, 0), (16, 9, 1),
       (16, 4, 4), (16, 1, 9), (16, 0, 16), (9, 16, 1),
       (9, 9, 0), (9, 4, 1), (9, 1, 4), (9, 0, 9),
       (4, 16, 4), (4, 9, 1), (4, 4, 0), (4, 1, 1),
       (4, 0, 4), (1, 16, 9), (1, 9, 4), (1, 4, 1),
       (1, 1, 0), (1, 0, 1), (0, 16, 16), (0, 9, 9),
       (0, 4, 4), (0, 1, 1), (0, 0, 0)] := by decide +kernel
  unfold a triangleClasses
  rw [hc, List.card_to_finset_eq_tree_set_size _ compare]
  decide +kernel

/-- The unit cube supplies exactly the three displayed squared-length classes. -/
@[category test, AMS 5 11 51]
theorem unit_cube_classes :
    triangleClasses 1 = {[1, 1, 2], [1, 2, 3], [2, 2, 2]} := by
  unfold triangleClasses
  decide +kernel

/-- The coordinate encoding agrees with the paper's first three contribution counts. -/
@[category test, AMS 5 11 51]
theorem small_coordinate_counts :
    (coordinateContributions 0).length = 1 ∧
      (coordinateContributions 1).length = 4 ∧
      (coordinateContributions 2).length = 10 := by
  decide +kernel

/-- Positive, degenerate, and impossible squared-length data remain distinct over integers. -/
@[category test, AMS 5 11 51]
theorem heron_polynomial_signs :
    heronPolynomial (1, 1, 2) = 4 ∧
      heronPolynomial (1, 1, 4) = 0 ∧
      heronPolynomial (1, 1, 9) = -45 := by
  decide +kernel

/-- Permuting squared side lengths does not create another congruence class. -/
@[category test, AMS 5 11 51]
theorem sorted_lengths_permutation :
    sortedLengths (3, 1, 2) = sortedLengths (2, 3, 1) := by
  decide +kernel

/--
Huber asks: "It is natural to ask whether" $a(n)\sqrt{\log n}/n^6$ "has a limit."
Does this normalized number of congruence classes converge to a finite real number?
-/
@[category research open, question, AMS 5 11 51]
theorem normalized_count_has_limit :
    ∃ L : ℝ, Tendsto (fun n : ℕ =>
      (a n : ℝ) * Real.sqrt (Real.log (n : ℝ)) / (n : ℝ) ^ 6) atTop (𝓝 L) := by
  sorry

end CubicalGridTriangles
