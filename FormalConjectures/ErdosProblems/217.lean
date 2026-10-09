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

import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-!
# Erdős Problem 217: crescent configurations

Source: https://www.erdosproblems.com/217 and the supplied 217.pdf, pp. 1–3.
The supplied source labels the classification problem OPEN.

Verified with Lean v4.35.0-rc3 and Mathlib commit
25730c7c759d108ef87ab70af2342a196760f79d (2026-10-01).

`Admissible n` formalizes the existence question for positive n.
`admissibleSizes` is the set the problem asks to determine.
`EventuallyImpossible` is the separate eventual-nonexistence conjecture.
Neither the classification nor that conjecture is asserted as a theorem.

The distance labels are indexed by multiplicity, NOT by increasing distance.
Pairs are counted once using their increasing indices. General position means
both no three collinear and no four concyclic points. No lattice restriction
or diameter bound is imposed. The unverified forum search reports are not
asserted as theorems in this file.

Convention: n = 0 is excluded; n = 1 has no pairs and no distance labels.
-/

namespace Erdos217

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Strictly increasing index pairs represent unordered pairs without repetition. -/
def pairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.1 < p.2

/-- The number of unordered pairs at Euclidean distance r. -/
noncomputable def multiplicity {n : ℕ} (p : Fin n → Plane) (r : ℝ) : ℕ := by
  classical
  exact ((pairs n).filter fun ij => dist (p ij.1) (p ij.2) = r).card

/-- The finite set of distances actually determined by the points. -/
noncomputable def distances {n : ℕ} (p : Fin n → Plane) : Finset ℝ := by
  classical
  exact (pairs n).image fun ij => dist (p ij.1) (p ij.2)

/-- The two general-position requirements, tested on distinct indexed points. -/
def GeneralPosition {n : ℕ} (p : Fin n → Plane) : Prop :=
  (∀ i j k, i < j → j < k → ¬ Collinear ℝ {p i, p j, p k}) ∧
  (∀ i j k l, i < j → j < k → k < l →
    ¬ EuclideanGeometry.Cospherical {p i, p j, p k, p l})

/-- Labels enumerate all distances, and label k has multiplicity k + 1. -/
def DistancePattern {n : ℕ} (p : Fin n → Plane) (d : Fin (n - 1) → ℝ) : Prop :=
  (∀ k, multiplicity p (d k) = k.val + 1) ∧
  (∀ i j, i < j → ∃ k, dist (p i) (p j) = d k)

/-- A positive size admitting exactly the configuration requested in Problem 217. -/
def Admissible (n : ℕ) : Prop :=
  0 < n ∧ ∃ p : Fin n → Plane,
    Function.Injective p ∧ GeneralPosition p ∧
    ∃ d : Fin (n - 1) → ℝ, DistancePattern p d

/-- The classification question is to determine this set. -/
def admissibleSizes : Set ℕ := {n | Admissible n}

/-- Erdős's separate conjecture: all sufficiently large sizes are impossible. -/
def EventuallyImpossible : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ¬ Admissible n

/-- Positive multiplicity means that the distance is actually attained. -/
theorem multiplicity_pos_iff {n : ℕ} (p : Fin n → Plane) (r : ℝ) :
    0 < multiplicity p r ↔ ∃ i j, i < j ∧ dist (p i) (p j) = r := by
  classical
  simp [multiplicity, pairs, Finset.card_pos, Finset.Nonempty]

/-- Distinct multiplicities force distinct distance labels. -/
theorem labels_injective {n : ℕ} {p : Fin n → Plane} {d : Fin (n - 1) → ℝ}
    (h : DistancePattern p d) : Function.Injective d := by
  intro a b hab
  have heq : a.val + 1 = b.val + 1 :=
    (h.1 a).symm.trans ((congrArg (multiplicity p) hab).trans (h.1 b))
  apply Fin.ext
  omega

/-- Every label is realized, including when the definition is used independently. -/
theorem label_realized {n : ℕ} {p : Fin n → Plane} {d : Fin (n - 1) → ℝ}
    (h : DistancePattern p d) (k : Fin (n - 1)) :
    ∃ i j, i < j ∧ dist (p i) (p j) = d k := by
  apply (multiplicity_pos_iff p (d k)).mp
  rw [h.1 k]
  exact Nat.zero_lt_succ _

/-- Distinct points ensure that none of the distance labels is zero or negative. -/
theorem label_pos {n : ℕ} {p : Fin n → Plane} {d : Fin (n - 1) → ℝ}
    (hp : Function.Injective p) (h : DistancePattern p d) (k : Fin (n - 1)) :
    0 < d k := by
  obtain ⟨i, j, hij, hd⟩ := label_realized h k
  rw [← hd]
  exact dist_pos.mpr (fun heq => (ne_of_lt hij) (hp heq))

/-- The enumerated labels are precisely the determined distances. -/
theorem distances_eq_labels {n : ℕ} {p : Fin n → Plane} {d : Fin (n - 1) → ℝ}
    (h : DistancePattern p d) : distances p = Finset.univ.image d := by
  classical
  ext r
  constructor
  · intro hr
    obtain ⟨⟨i, j⟩, hij, heq⟩ := Finset.mem_image.mp hr
    have hij' : i < j := (Finset.mem_filter.mp hij).2
    obtain ⟨k, hk⟩ := h.2 i j hij'
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk.symm.trans heq⟩
  · intro hr
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨i, j, hij, hd⟩ := label_realized h k
    exact Finset.mem_image.mpr ⟨(i, j), by simp [pairs, hij], hd⟩

/-- In particular, the statement really requires exactly n - 1 distinct distances. -/
theorem card_distances {n : ℕ} {p : Fin n → Plane} {d : Fin (n - 1) → ℝ}
    (h : DistancePattern p d) : (distances p).card = n - 1 := by
  classical
  rw [distances_eq_labels h, Finset.card_image_of_injective _ (labels_injective h)]
  simp

/-- The positivity convention prevents a spurious empty configuration. -/
theorem not_admissible_zero : ¬ Admissible 0 := by
  rintro ⟨h, _⟩
  exact (Nat.lt_irrefl 0) h

/-- Eventual impossibility is equivalent to finiteness of the set being classified. -/
theorem eventuallyImpossible_iff_finite : EventuallyImpossible ↔ admissibleSizes.Finite := by
  rw [Set.finite_iff_bddAbove]
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hn' : Admissible n := hn
    by_contra hle
    exact hN n (by omega) hn'
  · rintro ⟨N, hN⟩
    refine ⟨N + 1, ?_⟩
    intro n hn ha
    have hle : n ≤ N := hN ha
    omega

end Erdos217
