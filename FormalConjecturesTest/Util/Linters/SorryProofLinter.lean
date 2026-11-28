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
import FormalConjecturesUtil

/-!
# Tests for SorryProofLinter

`bad`, `badIndirect` and `UsesMarker` are built from a proof that is still `sorry` and are
reported. `good`, `fine` and the `answer` placeholder are not.
-/

set_option linter.style.sorryProof true
set_option linter.style.namespace false

namespace SorryProofLinterTest

theorem exists_one : ∃ n : ℕ, n = 1 := by
  sorry

theorem exists_one' : ∃ n : ℕ, n = 1 := exists_one

theorem exists_two : ∃ n : ℕ, n = 2 := ⟨2, rfl⟩

/--
warning: `SorryProofLinterTest.bad` is built from the proof of `SorryProofLinterTest.exists_one`, which is still `sorry`, so every statement that mentions `SorryProofLinterTest.bad` depends on `sorryAx`. Avoid that proof here: for example, define the constant with `sInf` or `Classical.epsilon` of the same predicate.

Note: This linter can be disabled with `set_option linter.style.sorryProof false`
-/
#guard_msgs(warning) in
noncomputable def bad := Classical.choose exists_one

/--
warning: `SorryProofLinterTest.badIndirect` is built from the proof of `SorryProofLinterTest.exists_one`, which is still `sorry`, so every statement that mentions `SorryProofLinterTest.badIndirect` depends on `sorryAx`. Avoid that proof here: for example, define the constant with `sInf` or `Classical.epsilon` of the same predicate.

Note: This linter can be disabled with `set_option linter.style.sorryProof false`
-/
#guard_msgs(warning) in
noncomputable def badIndirect := Classical.choose exists_one'

#guard_msgs(warning) in
noncomputable def good := sInf {n : ℕ | n = 1}

#guard_msgs(warning) in
noncomputable def fine := Classical.choose exists_two

#guard_msgs(warning) in
def foo.answer : ℕ := sorry

class Marker : Prop where
  holds : True

theorem marker : Marker := by
  sorry

/--
warning: `SorryProofLinterTest.UsesMarker` is built from the proof of `SorryProofLinterTest.marker`, which is still `sorry`, so every statement that mentions `SorryProofLinterTest.UsesMarker` depends on `sorryAx`. Avoid that proof here: for example, define the constant with `sInf` or `Classical.epsilon` of the same predicate.

Note: This linter can be disabled with `set_option linter.style.sorryProof false`
-/
#guard_msgs(warning) in
structure UsesMarker where
  val : ℕ
  proof : @Marker.holds marker = @Marker.holds marker

end SorryProofLinterTest
