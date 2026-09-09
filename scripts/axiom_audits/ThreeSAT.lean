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
import FormalConjecturesTest.ForMathlib.Computability.ThreeSAT

-- Transitive audit of the completed named definitions, theorems, and regression results.
#print axioms Computability.ThreeSAT.Literal
#print axioms Computability.ThreeSAT.Clause
#print axioms Computability.ThreeSAT.Formula
#print axioms Computability.ThreeSAT.Satisfiable
#print axioms Computability.ThreeSAT.eval
#print axioms Computability.ThreeSAT.eval_eq_true
#print axioms Computability.ThreeSAT.referenceCheck
#print axioms Computability.ThreeSAT.referenceCheck_eq_true
#print axioms Computability.ThreeSAT.rename
#print axioms Computability.ThreeSAT.eval_rename
#print axioms Computability.ThreeSAT.satisfiable_rename_equiv
#print axioms Computability.ThreeSAT.Test.positiveClause
#print axioms Computability.ThreeSAT.Test.negativeClause
#print axioms Computability.ThreeSAT.Test.sparseFormula
