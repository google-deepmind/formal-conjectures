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

public import FormalConjecturesForMathlib.Computability.BooleanSatisfiability
public import FormalConjecturesForMathlib.Computability.Complexity
public import Mathlib.LinearAlgebra.Matrix.Permanent

/-!
# Exact counting of assignments and Boolean-matrix permanents

Counts use binary natural-number output. Formula variables are precisely the
names occurring in the formula, not an implicit range determined by their
maximum binary name. Repeated occurrences do not create new assignments.
Matrices are explicit row lists; nonsquare inputs are assigned zero.

References: Valiant, *The Complexity of Computing the Permanent* (1979),
Theorem1 and §2, pp.189–193, https://doi.org/10.1016/0304-3975(79)90044-6.
The finite sums below specify answers, not efficient implementations.
-/

@[expose] public section

namespace ExactCounting

open Computability.BooleanSatisfiability

def satisfyingAssignments (f : Formula) : Finset (Finset ℕ) :=
  (support f).powerset.filter fun s =>
    ∀ clause ∈ f, (clause.map (evalLiteral s)).any id = true

def modelCount (f : Formula) : ℕ := (satisfyingAssignments f).card

theorem mem_satisfyingAssignments (f : Formula) (s : Finset ℕ) :
    s ∈ satisfyingAssignments f ↔
      s ⊆ support f ∧ ∀ clause ∈ f, (clause.map (evalLiteral s)).any id = true := by
  simp [satisfyingAssignments]

theorem modelCount_pos_iff (f : Formula) :
    0 < modelCount f ↔ SatisfiableWith (fun v => v.any id) f := by
  simp only [modelCount, Finset.card_pos, Finset.nonempty_iff_ne_empty]
  rw [← Finset.nonempty_iff_ne_empty]
  simp [Finset.Nonempty, mem_satisfyingAssignments, SatisfiableWith]

theorem modelCount_le (f : Formula) : modelCount f ≤ 2 ^ (support f).card := by
  simpa [modelCount, satisfyingAssignments, Finset.card_powerset] using
    Finset.card_le_card (Finset.filter_subset
      (fun s => ∀ clause ∈ f, (clause.map (evalLiteral s)).any id = true) (support f).powerset)

abbrev BooleanMatrix := List (List Bool)

def Square (a : BooleanMatrix) : Prop := ∀ row ∈ a, row.length = a.length

instance (a : BooleanMatrix) : Decidable (Square a) := by unfold Square; infer_instance

def toMatrix (a : BooleanMatrix) : Matrix (Fin a.length) (Fin a.length) ℕ :=
  fun i j => ((a[i.val]?.getD [])[j.val]?.getD false).toNat

def permanent (a : BooleanMatrix) : ℕ :=
  if Square a then (toMatrix a).permanent else 0

theorem permanent_eq (a : BooleanMatrix) (h : Square a) :
    permanent a = (toMatrix a).permanent := by simp [permanent, h]

theorem permanent_nonsquare (a : BooleanMatrix) (h : ¬ Square a) :
    permanent a = 0 := by simp [permanent, h]

@[simp] theorem permanent_empty : permanent [] = 1 := by
  simp [permanent, Square, Matrix.permanent_isEmpty]

end ExactCounting
