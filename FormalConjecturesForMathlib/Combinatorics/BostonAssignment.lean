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

public import FormalConjecturesForMathlib.Combinatorics.FiniteAssignment
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.List.FinRange

/-!
# Boston assignment with common priorities

There are $n$ students and $n$ single-seat schools. Students have complete strict rankings,
and every school gives priority to students in increasing order of their labels.
Assignments are permanent. In each round of naive Boston, unmatched students apply to their
next ranked school. A vacant school accepts its highest-priority applicant from that round.

Reference: G. Pritchard and M. C. Wilson, *Asymptotic Welfare Performance of Boston Assignment
Algorithms* (2023), Section 1.1, https://doi.org/10.1287/stsy.2022.0104.
-/

@[expose] public section

namespace BostonAssignment

/-- Complete strict student rankings, mapping schools to zero-based ranks. -/
abbrev Preferences (n : ℕ) := FiniteAssignment.Preferences n

/-- A partial assignment maps each student to their assigned school, if any. -/
abbrev Assignment (n : ℕ) := FiniteAssignment.Assignment n

/-- The school a student applies to in a zero-based round of naive Boston. -/
def bid {n : ℕ} (p : Preferences n) (round : ℕ) (student : Fin n) : Option (Fin n) :=
  if h : round < n then some ((p student).symm ⟨round, h⟩) else none

/-- Process one round's applications in the common priority order. -/
def runRound {n : ℕ} (p : Preferences n) (round : ℕ)
    (start : Assignment n) : Assignment n :=
  (List.finRange n).foldl (fun current student ↦
    if current student = none then
      match bid p round student with
      | none => current
      | some school =>
        if ∀ i, current i ≠ some school then Function.update current student (some school)
        else current
    else current) start

/-- Run $n$ rounds of naive Boston, which finishes by then for complete strict rankings. -/
def outcome {n : ℕ} (p : Preferences n) : Assignment n :=
  (List.range n).foldl (fun state round ↦ runRound p round state) (fun _ ↦ none)

/-- One-based assigned rank, with zero for an unassigned student. -/
def assignedRank {n : ℕ} (p : Preferences n) (student : Fin n) : ℕ :=
  FiniteAssignment.assignedRank p (outcome p) student

/-- Largest assigned rank, or zero in the empty market. -/
def worstRank {n : ℕ} (p : Preferences n) : ℕ :=
  FiniteAssignment.worstRank p (outcome p)

/-- The largest assigned rank is at most the market size. -/
theorem worstRank_le {n : ℕ} (p : Preferences n) : worstRank p ≤ n := by
  exact FiniteAssignment.worstRank_le p (outcome p)

/-- The empty market has largest assigned rank zero. -/
theorem worstRank_zero (p : Preferences 0) : worstRank p = 0 := by
  simp [worstRank]

/-- A singleton student receives their first choice. -/
theorem assignedRank_one : assignedRank (fun _ ↦ Equiv.refl (Fin 1)) 0 = 1 := by
  decide

/-- Later rounds keep earlier acceptances, even when an applicant has higher priority. -/
theorem outcome_three :
    outcome ![Equiv.refl (Fin 3), Equiv.refl _, Equiv.swap 0 1] =
      ![some 0, some 2, some 1] := by
  decide

/-- A three-student market can assign a student their third choice. -/
theorem worstRank_three :
    worstRank ![Equiv.refl (Fin 3), Equiv.refl _, Equiv.swap 0 1] = 3 := by
  decide

end BostonAssignment
