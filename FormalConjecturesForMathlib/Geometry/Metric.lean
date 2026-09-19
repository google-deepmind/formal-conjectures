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
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Sym.Card
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Topology.MetricSpace.Defs

@[expose] public section

open scoped Finset

variable {X : Type*} [MetricSpace X]

/-- The number of pairs of points of a finite set `s` in a metric space that are distance 1 apart.
-/
noncomputable def unitDistNum (s : Finset X) : ℕ := #{p ∈ s.sym2 | dist p.out.1 p.out.2 = 1}

/-- The set of distances determined by a finite set of points in a metric space. -/
noncomputable def distanceSet (points : Finset X) : Finset ℝ :=
  points.offDiag.image fun (pair : X × X) => dist pair.1 pair.2

/--
Given a finite set of points in a metric space, we define the number of distinct distances
between pairs of points.
-/
noncomputable def distinctDistances (points : Finset X) : ℕ :=
  #(distanceSet points)

variable (X) in
/-- The minimum number of distinct distances determined by a set of `n` points in `X`. -/
noncomputable def minimalDistinctDistances (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ points : Finset X, #points = n ∧ distinctDistances points = m}

/-- The multiplicity of the distance `d` determined by `points`, that is, the number of unordered
pairs of distinct points at distance `d` apart. -/
noncomputable def distanceMultiplicity (points : Finset X) (d : ℝ) : ℕ :=
  #(points.offDiag.filter fun (pair : X × X) => dist pair.1 pair.2 = d) / 2

open Classical in
/-- Given a finite set of points in a metric space, we define the number of distinct distances
between a given point and all other points. -/
noncomputable def distinctDistancesFrom (points : Finset X) (pt : X) : ℕ :=
  #((points.erase pt).image fun x => dist x pt)

open Classical in
/-- The number of unit-distance pairs of a finite set of `n` points is at most $\binom{n}{2}$,
the total number of unordered pairs of distinct points. -/
theorem unitDistNum_le_choose_two (s : Finset X) : unitDistNum s ≤ (#s).choose 2 := by
  rw [unitDistNum, ← Sym2.card_image_offDiag]
  refine Finset.card_le_card fun p hp => ?_
  obtain ⟨hps, hpd⟩ := Finset.mem_filter.mp hp
  rw [← Finset.image_diag_union_image_offDiag (s := s), Finset.mem_union] at hps
  rcases hps with h | h
  · obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨-, rfl⟩ : _ ∧ x = y := Finset.mem_diag.mp hxy
    simp at hpd
  · exact h

/-- The ordered pairs of distinct points of `points` at distance `d` come in swapped pairs, so
there are evenly many of them. -/
theorem even_card_offDiag_filter_dist_eq (points : Finset X) (d : ℝ) :
    Even #(points.offDiag.filter fun (pair : X × X) => dist pair.1 pair.2 = d) := by
  set F := points.offDiag.filter fun (pair : X × X) => dist pair.1 pair.2 = d with hF
  rw [← ZMod.natCast_eq_zero_iff_even]
  have h : ∑ _a ∈ F, (1 : ZMod 2) = 0 := by
    refine Finset.sum_involution (fun a _ => a.swap) (fun a _ => by decide) ?_ ?_
      (fun a _ => Prod.swap_swap a)
    · intro a ha _ hsw
      have := (Finset.mem_offDiag.1 (Finset.mem_filter.1 ha).1).2.2
      exact this (Prod.ext_iff.1 hsw).1.symm
    · intro a ha
      obtain ⟨hoff, hd⟩ := Finset.mem_filter.1 ha
      obtain ⟨h1, h2, h3⟩ := Finset.mem_offDiag.1 hoff
      exact Finset.mem_filter.2 ⟨Finset.mem_offDiag.2 ⟨h2, h1, Ne.symm h3⟩, by
        simpa [dist_comm] using hd⟩
  simpa [Finset.sum_const, nsmul_eq_mul] using h

/-- The multiplicities of the distances determined by `points` add up to the number of
unordered pairs of distinct points. -/
theorem sum_distanceMultiplicity (points : Finset X) :
    ∑ d ∈ distanceSet points, distanceMultiplicity points d = (#points).choose 2 := by
  unfold distanceSet distanceMultiplicity
  rw [← Nat.sum_div (fun d _ => even_iff_two_dvd.1 (even_card_offDiag_filter_dist_eq points d)),
    ← Finset.card_eq_sum_card_image (fun (pair : X × X) => dist pair.1 pair.2) points.offDiag,
    Finset.offDiag_card, Nat.choose_two_right]
  rcases Nat.eq_zero_or_pos #points with h | h
  · simp [h]
  · rw [Nat.mul_sub_one]
