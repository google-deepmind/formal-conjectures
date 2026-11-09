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

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Real.Basic

/-!
# Ranks in finite assignments

Complete strict rankings map candidate labels to zero-based ranks. Assignment states may leave
students unassigned. Their assigned rank is extended by zero at an unassigned student; a
permutation gives a complete feasible assignment. The welfare statistics do not specify a
mechanism or a priority distribution.
-/

@[expose] public section

namespace FiniteAssignment

/-- Complete strict student rankings of schools. -/
abbrev Preferences (n : ℕ) := Fin n → Equiv.Perm (Fin n)

/-- An assignment state gives each student a school or leaves them unassigned. -/
abbrev Assignment (n : ℕ) := Fin n → Option (Fin n)

/-- The one-based rank a student assigns to a school. -/
def rank {n : ℕ} (p : Preferences n) (i j : Fin n) : ℕ := (p i j).val + 1

/-- A complete bijective assignment viewed as an assignment state. -/
def ofPerm {n : ℕ} (a : Equiv.Perm (Fin n)) : Assignment n := fun i ↦ some (a i)

/-- One-based assigned rank, extended by zero for an unassigned student. -/
def assignedRank {n : ℕ} (p : Preferences n) (a : Assignment n) (i : Fin n) : ℕ :=
  (a i).elim 0 (rank p i)

/-- The mean assigned rank, with zero for unassigned students and the empty market. -/
noncomputable def averageRank {n : ℕ} (p : Preferences n) (a : Assignment n) : ℝ :=
  (∑ i, (assignedRank p a i : ℝ)) / n

/-- The largest assigned rank, or zero in the empty market. -/
def worstRank {n : ℕ} (p : Preferences n) (a : Assignment n) : ℕ :=
  Finset.univ.sup (assignedRank p a)

/-- A full assignment's assigned rank is its one-based preference rank. -/
@[simp] theorem assignedRank_ofPerm {n : ℕ} (p : Preferences n)
    (a : Equiv.Perm (Fin n)) (i : Fin n) :
    assignedRank p (ofPerm a) i = rank p i (a i) := rfl

/-- Every assigned rank is at most the number of schools. -/
theorem assignedRank_le {n : ℕ} (p : Preferences n) (a : Assignment n) (i : Fin n) :
    assignedRank p a i ≤ n := by
  unfold assignedRank
  cases a i with
  | none => exact Nat.zero_le _
  | some j => exact (p i j).isLt

/-- The largest assigned rank is at most the number of schools. -/
theorem worstRank_le {n : ℕ} (p : Preferences n) (a : Assignment n) : worstRank p a ≤ n :=
  Finset.sup_le fun i _ ↦ assignedRank_le p a i

/-- The empty market has average assigned rank zero. -/
@[simp] theorem averageRank_zero (p : Preferences 0) (a : Assignment 0) :
    averageRank p a = 0 := by
  simp [averageRank]

/-- The empty market has largest assigned rank zero. -/
@[simp] theorem worstRank_zero (p : Preferences 0) (a : Assignment 0) : worstRank p a = 0 := by
  simp [worstRank]

/-- A full singleton assignment gives its student their first choice. -/
@[simp] theorem averageRank_one (p : Preferences 1) (a : Equiv.Perm (Fin 1)) :
    averageRank p (ofPerm a) = 1 := by
  simp [averageRank, rank]

end FiniteAssignment
