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
public import FormalConjecturesForMathlib.Combinatorics.StableMarriage

/-!
# Deterministic school-choice mechanisms

There are equally many students and single-seat schools. In `StableMarriage.Profile`,
`manRank` gives student preferences and `womanRank` gives school priorities. All rankings
are complete and strict. A feasible deterministic mechanism returns a bijective assignment.

Reference: J. Ortega and T. Klein, *The Cost of Strategy-Proofness in School Choice* (2023),
https://doi.org/10.1016/j.geb.2023.07.008.
-/

@[expose] public section

namespace SchoolChoice

/-- A deterministic mechanism assigns every student a different school. -/
abbrev Mechanism (n : ℕ) := StableMarriage.Profile n → Equiv.Perm (Fin n)

/-- Change one student's report while keeping all school priorities fixed. -/
def updateReport {n : ℕ} (p : StableMarriage.Profile n) (i : Fin n)
    (report : Equiv.Perm (Fin n)) : StableMarriage.Profile n :=
  ⟨Function.update p.manRank i report, p.womanRank⟩

/-- The deviating student's reported ranking is the replacement ranking. -/
@[simp] theorem updateReport_manRank_self {n : ℕ} (p : StableMarriage.Profile n) (i : Fin n)
    (report : Equiv.Perm (Fin n)) : (updateReport p i report).manRank i = report := by
  simp [updateReport]

/-- Student reports do not change school priorities. -/
@[simp] theorem updateReport_womanRank {n : ℕ} (p : StableMarriage.Profile n) (i : Fin n)
    (report : Equiv.Perm (Fin n)) : (updateReport p i report).womanRank = p.womanRank := rfl

/-- The one-based rank that a student gives to a school. -/
def rank {n : ℕ} (p : StableMarriage.Profile n) (i j : Fin n) : ℕ :=
  FiniteAssignment.rank p.manRank i j

/-- No student can improve by changing their report, at any profile and fixed priorities.
Both assignments are evaluated using the student's true ranking. -/
def StudentStrategyProof {n : ℕ} (f : Mechanism n) : Prop :=
  ∀ p i report, rank p i (f p i) ≤ rank p i (f (updateReport p i report) i)

/-- The students' average one-based assigned rank, or zero in an empty market. -/
noncomputable def averageRank {n : ℕ} (p : StableMarriage.Profile n)
    (assignment : Equiv.Perm (Fin n)) : ℝ :=
  FiniteAssignment.averageRank p.manRank (FiniteAssignment.ofPerm assignment)

/-- Expected average rank under independent uniform student rankings and school priorities. -/
noncomputable def expectedAverageRank {n : ℕ} (f : Mechanism n) : ℝ :=
  ∫ p, averageRank p (f p) ∂((StableMarriage.uniformProfile n).toMeasure)

/-- A mechanism that always chooses the same assignment is student-strategy-proof. -/
theorem studentStrategyProof_const {n : ℕ} (assignment : Equiv.Perm (Fin n)) :
    StudentStrategyProof (fun _ ↦ assignment) := by
  intro p i report
  exact le_refl _

/-- The empty market has average rank zero. -/
theorem averageRank_zero (p : StableMarriage.Profile 0) (assignment : Equiv.Perm (Fin 0)) :
    averageRank p assignment = 0 := by
  simp [averageRank]

/-- A single student receives their first choice under every feasible assignment. -/
theorem averageRank_one (p : StableMarriage.Profile 1) (assignment : Equiv.Perm (Fin 1)) :
    averageRank p assignment = 1 := by
  simp [averageRank]

/-- Every feasible mechanism has expected average rank one in a singleton market. -/
theorem expectedAverageRank_one (f : Mechanism 1) : expectedAverageRank f = 1 := by
  simp [expectedAverageRank, averageRank_one]

end SchoolChoice
