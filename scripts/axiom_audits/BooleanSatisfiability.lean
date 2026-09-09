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
import FormalConjecturesTest.ForMathlib.Computability.BooleanSatisfiability

/-! # Axiom audit for Boolean satisfiability definitions and proved infrastructure -/

#print axioms ComplexityTheory.HasPolyTimeDecider
#print axioms ComplexityTheory.hasPolyTimeDecider_congr
#print axioms ComplexityTheory.IsPolyTime.hasPolyTimeDecider
#print axioms Computability.BooleanSatisfiability.Literal
#print axioms Computability.BooleanSatisfiability.Formula
#print axioms Computability.BooleanSatisfiability.PositiveFormula
#print axioms Computability.BooleanSatisfiability.support
#print axioms Computability.BooleanSatisfiability.mem_support
#print axioms Computability.BooleanSatisfiability.evalLiteral
#print axioms Computability.BooleanSatisfiability.SatisfiableWith
#print axioms Computability.BooleanSatisfiability.evalLiteral_restrict
#print axioms Computability.BooleanSatisfiability.satisfiableWith_iff
#print axioms Computability.BooleanSatisfiability.ExactlyThree
#print axioms Computability.BooleanSatisfiability.ThreeSat
#print axioms Computability.BooleanSatisfiability.OneInThree
#print axioms Computability.BooleanSatisfiability.NotAllEqual
#print axioms Computability.BooleanSatisfiability.positiveEmbedding
#print axioms Computability.BooleanSatisfiability.PositiveOneInThree
#print axioms Computability.BooleanSatisfiability.PositiveNotAllEqual
#print axioms Computability.BooleanSatisfiability.positiveOneInThree_iff
#print axioms Computability.BooleanSatisfiability.positiveNotAllEqual_iff
#print axioms Computability.BooleanSatisfiability.Test.nonvacuous_machine_interface
