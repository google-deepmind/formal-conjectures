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
# Uniqueness of minimum-surface integral boxes

For positive volume $n$ and dimension $k\ge 2$, minimize the surface of a box with positive
integer edges and product exactly $n$. Rotgé and Tenenbaum ask whether the minimizing tuple
of edge lengths is unique after arranging its entries in increasing order. They prove
uniqueness in dimension two and report numerical verification for dimensions three through
five and volumes at most $10^8$.

Every edge of a positive integer box of volume $n$ is at most $n$, so a finite tuple type
contains every admissible box. The objective is half the surface, which has the same
minimizers as the surface itself.

*References:*
* J. Rotgé and G. Tenenbaum,
  [On integral boxes of minimal surface](https://arxiv.org/abs/2602.02349),
  Introduction, the question following equation (1.1).
* [OEIS A075777](https://oeis.org/A075777), the three-dimensional exact-volume surface count.
* [OEIS A400004](https://oeis.org/A400004), a related problem allowing volume at least $n$.
-/

@[expose] public section

namespace Arxiv.«2602.02349»

/-- A finite domain containing every positive integer edge tuple of volume $n$. -/
abbrev SideTuple (n k : ℕ) := Fin k → Fin (n + 1)

/-- Half the surface of a box is the sum of the products of all but one of its edges. -/
def halfSurfaceArea {n k : ℕ} (d : SideTuple n k) : ℕ :=
  ∑ i : Fin k, ∏ j ∈ Finset.univ.erase i, (d j : ℕ)

/-- Admissible edge tuples are positive, sorted, and have product exactly the given volume. -/
def IsAdmissible {n k : ℕ} (d : SideTuple n k) : Prop :=
  (∀ i, 0 < (d i : ℕ)) ∧ Monotone d ∧ (∏ i, (d i : ℕ)) = n

instance {n k : ℕ} (d : SideTuple n k) : Decidable (IsAdmissible d) := by
  unfold IsAdmissible Monotone
  infer_instance

/-- An admissible tuple minimizes the surface among every admissible tuple of the same volume. -/
def IsMinimizer {n k : ℕ} (d : SideTuple n k) : Prop :=
  IsAdmissible d ∧
    ∀ e : SideTuple n k, IsAdmissible e → halfSurfaceArea d ≤ halfSurfaceArea e

instance {n k : ℕ} (d : SideTuple n k) : Decidable (IsMinimizer d) := by
  unfold IsMinimizer
  infer_instance

/-- Positivity and fixed volume justify the finite upper bound on every edge. -/
@[category API, AMS 11 52]
theorem edge_le_volume {n k : ℕ} (d : Fin k → ℕ)
    (hpos : ∀ i, 0 < d i) (hvol : ∏ i, d i = n) (i : Fin k) : d i ≤ n := by
  calc
    d i ≤ ∏ j, d j :=
      Finset.single_le_prod' (fun j _ => hpos j) (Finset.mem_univ i)
    _ = n := hvol

@[category test, AMS 11 52]
theorem unique_unit_square : ∃! d : SideTuple 1 2, IsMinimizer d := by
  unfold ExistsUnique
  decide +kernel

@[category test, AMS 11 52]
theorem unique_unit_cube : ∃! d : SideTuple 1 3, IsMinimizer d := by
  unfold ExistsUnique
  decide +kernel

@[category test, AMS 11 52]
theorem unique_volume_two_cube : ∃! d : SideTuple 2 3, IsMinimizer d := by
  unfold ExistsUnique
  decide +kernel

@[category test, AMS 11 52]
theorem unique_volume_three_cube : ∃! d : SideTuple 3 3, IsMinimizer d := by
  unfold ExistsUnique
  decide +kernel

@[category test, AMS 11 52]
theorem unique_volume_four_cube : ∃! d : SideTuple 4 3, IsMinimizer d := by
  unfold ExistsUnique
  decide +kernel

/-- The sorted volume-four optimizer is the box with edges $1,2,2$. -/
@[category test, AMS 11 52]
theorem volume_four_minimizer : IsMinimizer (n := 4) ![1, 2, 2] := by
  decide +kernel

/-- The box with edges $1,1,4$ has the right volume but a larger surface. -/
@[category test, AMS 11 52]
theorem volume_four_long_box_not_minimal :
    IsAdmissible (n := 4) ![1, 1, 4] ∧ ¬ IsMinimizer (n := 4) ![1, 1, 4] := by
  decide +kernel

/-- Sorting removes the permutation multiplicity of the same box. -/
@[category test, AMS 11 52]
theorem nonsorted_permutation_excluded :
    ¬ IsAdmissible (n := 4) ![2, 1, 2] ∧
      halfSurfaceArea (n := 4) ![2, 1, 2] = halfSurfaceArea (n := 4) ![1, 2, 2] := by
  decide +kernel

/-- Positive edge lengths cannot give a zero-volume box. -/
@[category test, AMS 11 52]
theorem no_zero_volume_cube : ¬ ∃ d : SideTuple 0 3, IsAdmissible d := by
  decide +kernel

/-- The facet formula has the expected values in dimensions two, three, and four. -/
@[category test, AMS 11 52]
theorem small_half_surface_areas :
    halfSurfaceArea (n := 6) ![2, 3] = 5 ∧
      halfSurfaceArea (n := 6) ![1, 2, 3] = 11 ∧
      halfSurfaceArea (n := 2) ![1, 1, 1, 2] = 7 := by
  decide +kernel

/--
Is the sorted tuple of edge lengths of a minimum-surface integral box unique for every
positive volume and every dimension at least two? Rotgé and Tenenbaum write:
"We leave this question open for the time being" after discussing uniqueness of $(P_{n,k})$.
-/
@[category research open, question, AMS 11 52]
theorem minimum_surface_box_unique :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 2 ≤ k → ∃! d : SideTuple n k, IsMinimizer d := by
  sorry

end Arxiv.«2602.02349»
