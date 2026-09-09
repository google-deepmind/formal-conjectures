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
import FormalConjecturesTest.ForMathlib.Computability.FiniteSetProblems

/-! # Axiom audit for finite-set problem definitions and proved infrastructure -/

#print axioms ComplexityTheory.HasPolyTimeDecider
#print axioms ComplexityTheory.hasPolyTimeDecider_congr
#print axioms ComplexityTheory.IsPolyTime.hasPolyTimeDecider
#print axioms Computability.FiniteSetProblems.Family
#print axioms Computability.FiniteSetProblems.row
#print axioms Computability.FiniteSetProblems.covered
#print axioms Computability.FiniteSetProblems.ground
#print axioms Computability.FiniteSetProblems.row_subset_ground
#print axioms Computability.FiniteSetProblems.DisjointRows
#print axioms Computability.FiniteSetProblems.SetPacking
#print axioms Computability.FiniteSetProblems.SetCovering
#print axioms Computability.FiniteSetProblems.ValidFamily
#print axioms Computability.FiniteSetProblems.ExactCover
#print axioms Computability.FiniteSetProblems.ExactCover.ground_eq
#print axioms Computability.FiniteSetProblems.ExactHitting
#print axioms Computability.FiniteSetProblems.exactHitting_iff
#print axioms Computability.FiniteSetProblems.Triple
#print axioms Computability.FiniteSetProblems.MatchingInput
#print axioms Computability.FiniteSetProblems.ValidMatching
#print axioms Computability.FiniteSetProblems.CoordinateDisjoint
#print axioms Computability.FiniteSetProblems.ThreeDimensionalMatching
#print axioms Computability.FiniteSetProblems.Test.nonvacuous_machine_interface
