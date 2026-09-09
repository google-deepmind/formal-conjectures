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
import FormalConjecturesTest.ForMathlib.Computability.NumericalProblems

/-! # Axiom audit for numerical decision problems and proved infrastructure -/

#print axioms ComplexityTheory.HasPolyTimeDecider
#print axioms ComplexityTheory.hasPolyTimeDecider_congr
#print axioms ComplexityTheory.IsPolyTime.hasPolyTimeDecider
#print axioms Computability.NumericalProblems.selectedSum
#print axioms Computability.NumericalProblems.selectedSum_empty
#print axioms Computability.NumericalProblems.SubsetSum
#print axioms Computability.NumericalProblems.Partition
#print axioms Computability.NumericalProblems.selectedSum_add_compl
#print axioms Computability.NumericalProblems.partition_iff
#print axioms Computability.NumericalProblems.IntegerProgramInput
#print axioms Computability.NumericalProblems.ValidIntegerProgram
#print axioms Computability.NumericalProblems.coefficient
#print axioms Computability.NumericalProblems.ZeroOneProgramming
#print axioms Computability.NumericalProblems.zeroOneProgramming_iff
#print axioms Computability.NumericalProblems.Job
#print axioms Computability.NumericalProblems.ValidJobs
#print axioms Computability.NumericalProblems.completionTime
#print axioms Computability.NumericalProblems.latePenalty
#print axioms Computability.NumericalProblems.JobSequencing
#print axioms Computability.NumericalProblems.WeightMatrix
#print axioms Computability.NumericalProblems.weight
#print axioms Computability.NumericalProblems.ValidWeightMatrix
#print axioms Computability.NumericalProblems.cutWeight
#print axioms Computability.NumericalProblems.cutWeight_compl
#print axioms Computability.NumericalProblems.WeightedMaxCut
#print axioms Computability.NumericalProblems.Test.nonvacuous_machine_interface
