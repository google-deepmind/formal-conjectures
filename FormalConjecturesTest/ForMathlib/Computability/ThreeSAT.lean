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

public meta import FormalConjecturesForMathlib.Computability.ThreeSAT
public import FormalConjecturesForMathlib.Computability.ThreeSAT

/-! # Regression proofs for structured 3-CNF semantics -/

@[expose] public section

namespace Computability.ThreeSAT.Test

def positiveClause : Clause 1 := ⟨[⟨0, true⟩], by decide⟩
def negativeClause : Clause 1 := ⟨[⟨0, false⟩], by decide⟩
def sparseFormula : Formula 5 := [⟨[⟨4, true⟩, ⟨1, false⟩], by decide⟩]

example : referenceCheck ([] : Formula 0) = true := by decide
example : referenceCheck ([⟨[], by decide⟩] : Formula 0) = false := by decide
example : referenceCheck [positiveClause] = true := by decide
example : referenceCheck [positiveClause, negativeClause] = false := by decide
example : referenceCheck sparseFormula = true := by decide
example : eval sparseFormula (fun _ ↦ false) = true := by decide
example : eval sparseFormula (fun i ↦ decide (i.val = 1)) = false := by decide
/-- info: (true, false) -/
#guard_msgs in
#eval (referenceCheck [positiveClause], referenceCheck [positiveClause, negativeClause])

end Computability.ThreeSAT.Test
