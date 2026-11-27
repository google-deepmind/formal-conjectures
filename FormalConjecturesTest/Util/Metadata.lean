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

public meta import FormalConjecturesUtil.Metadata

/-! Tests for `FormalConjectures.Metadata.openSteps` and `restsOn`. -/

@[expose] public section

namespace OpenStepsTest

theorem stated : 1 = 1 := by
  sorry

theorem reduction : 1 = 1 ∧ True := ⟨stated, trivial⟩

theorem twoSteps : True ∧ (1 = 1 ∧ True) := ⟨trivial, reduction⟩

theorem proved : 2 = 2 := rfl

theorem computed : 2 + 2 = 4 := by native_decide

end OpenStepsTest

open Lean FormalConjectures.Metadata in
run_meta do
  -- A proof that reaches an open statement names it, through any number of steps.
  guard <| (← openSteps ``OpenStepsTest.reduction) == #[``OpenStepsTest.stated]
  guard <| (← openSteps ``OpenStepsTest.twoSteps) == #[``OpenStepsTest.stated]
  -- An open statement does not list itself, and a finished proof rests on nothing.
  guard <| (← openSteps ``OpenStepsTest.stated) == #[]
  guard <| (← openSteps ``OpenStepsTest.proved) == #[]
  -- `restsOn` adds what is beyond the standard axioms; native evaluation shows as `native`.
  guard <| (← restsOn ``OpenStepsTest.reduction) == #["OpenStepsTest.stated"]
  guard <| (← restsOn ``OpenStepsTest.proved) == #[]
  guard <| (← restsOn ``OpenStepsTest.computed) == #["native"]
