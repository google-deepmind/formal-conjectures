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

import FormalConjectures.Util.ProblemImports

open Nat Int Finset

/--
A255916: Number of ways to write $n$ as the sum of a generalized heptagonal number, an octagonal number and a nonagonal number.
$$ a(n) = \# \left\{ (k, x, y) \in \mathbb{Z} \times \mathbb{N} \times \mathbb{N} \mid G_7(k) + P_8(x) + P_9(y) = n \right\} $$
where the generalized heptagonal number is $G_7(k) = \frac{5k^2 - 3k}{2}$, the octagonal number is $P_8(x) = 3x^2 - 2x$, and the nonagonal number is $P_9(y) = \frac{7y^2 - 5y}{2}$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- Generalized heptagonal number G_7(k) for k in Z.
  let generalized_heptagonal_num (k : ℤ) : ℕ :=
    ((5 * k ^ 2 - 3 * k) / 2).toNat

  -- Octagonal number P_8(x) for x in N.
  let octagonal_num (x : ℕ) : ℕ :=
    x * (3 * x - 2)

  -- Nonagonal number P_9(y) for y in N.
  let nonagonal_num (y : ℕ) : ℕ :=
    y * (7 * y - 5) / 2

  -- Bounds for iteration: n+1 is a safe upper bound for all indices.
  let N_bound : ℕ := n + 1
  let Z_bound_pos : ℤ := N_bound

  -- Define finite sets for iteration.
  let K_set : Finset ℤ := Finset.Icc (-Z_bound_pos) Z_bound_pos
  let X_set : Finset ℕ := Finset.range N_bound
  let Y_set : Finset ℕ := Finset.range N_bound

  -- The number of solutions is the sum of 1 for each valid triplet (k, x, y).
  Finset.sum K_set fun k =>
    Finset.sum X_set fun x =>
      Finset.sum Y_set fun y =>
        if generalized_heptagonal_num k + octagonal_num x + nonagonal_num y = n then 1 else 0

theorem a_zero : a 0 = 1 := by sorry
theorem a_one : a 1 = 3 := by sorry
theorem a_two : a 2 = 3 := by sorry
theorem a_three : a 3 = 1 := by sorry

-- General polygonal number definitions for the conjecture
section PolygonalNumbers

open Int
open scoped Classical

/-- The m-th generalized polygonal number is G_m(k) = ((m-2)*k^2 - (m-4)*k) / 2.
    We define it as a natural number. -/
noncomputable def generalized_polygonal_num_of_sides (m : ℕ) (k : ℤ) : ℕ :=
  if h : m ≥ 3 then
    let m' := (m : ℤ)
    let val := (m' - 2) * k ^ 2 - (m' - 4) * k
    (val / 2).toNat -- Int division
  else 0

/-- The m-th non-generalized polygonal number (for x ≥ 0) is P_m(x) = ((m-2)*x^2 - (m-4)*x) / 2. -/
noncomputable def polygonal_num_of_sides (m : ℕ) (x : ℕ) : ℕ :=
  if h : m ≥ 3 then
    let m' := (m : ℤ)
    let x' := (x : ℤ)
    let val := (m' - 2) * x' ^ 2 - (m' - 4) * x'
    (val / 2).toNat -- Int division
  else 0

/-- Predicate asserting that n can be written as the sum of a generalized heptagonal number (G_7),
and two non-generalized polygonal numbers P_j and P_k. -/
def is_sum_of_G7_Pj_Pk (n j k : ℕ) : Prop :=
  ∃ (z : ℤ) (x y : ℕ),
    generalized_polygonal_num_of_sides 7 z + polygonal_num_of_sides j x + polygonal_num_of_sides k y = n

/-- The set of ordered pairs (j, k) from the conjecture's statement. -/
def sun_polygonal_pairs_set : Finset (ℕ × ℕ) :=
  -- (3, k) for k = 3..19, 21..24, 26, 27, 29, 30
  let k_vals_j3 : Finset ℕ := (Icc 3 19) ∪ (Icc 21 24) ∪ {26, 27, 29, 30}
  let set3_k := k_vals_j3.image (fun k => (3, k))

  -- (4, k) for k = 4..11, 13, 14, 17, 19, 20, 23, 26
  let k_vals_j4 : Finset ℕ := (Icc 4 11) ∪ {13, 14, 17, 19, 20, 23, 26}
  let set4_k := k_vals_j4.image (fun k => (4, k))

  set3_k ∪ set4_k ∪ {(5, 6), (5, 9), (6, 7), (8, 9)}

end PolygonalNumbers

/--
Conjecture: (i) a(n) > 0 for all n. Moreover, for k >= j >=3, every nonnegative integer can be
written as the sum of a generalized heptagonal number, a j-gonal number and a k-gonal number,
if and only if (j,k) is among the following ordered pairs:
(3,k) (k = 3..19, 21..24, 26, 27, 29, 30), (4,k) (k = 4..11, 13, 14, 17, 19, 20, 23, 26),
(5,6), (5,9), (6,7), (8,9).
-/
theorem oeis_255916_conjecture_i :
  (∀ (n : ℕ), a n > 0)
  ∧
  (∀ (j k : ℕ),
    3 ≤ j ∧ j ≤ k →
    ((∀ (n : ℕ), is_sum_of_G7_Pj_Pk n j k) ↔ (j, k) ∈ sun_polygonal_pairs_set)) :=
by sorry
