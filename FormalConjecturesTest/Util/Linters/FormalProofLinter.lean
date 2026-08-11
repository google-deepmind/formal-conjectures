/-
Copyright 2025 The Formal Conjectures Authors.

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

public meta import FormalConjecturesUtil.Linters.FormalProofLinter

@[expose] public section

set_option linter.style.conditional_formal_proof true

namespace FormalProofLinter

/-- An assumption that is still open, which is the ordinary case. -/
theorem an_open_assumption : 0 = 0 := by
  sorry

#guard_msgs in
/-- A proof conditional on something nobody has proved. -/
@[category research solved,
  conditional formal_proof using lean4 at "https://github.com/example/conditional"
    assuming an_open_assumption]
theorem conditional_on_an_open_assumption : 4 + 4 = 8 := by
  rfl

/-- An assumption that has since been proved. -/
theorem a_proved_assumption : 2 = 2 := by
  rfl

/--
warning: The assumed hypothesis `FormalProofLinter.a_proved_assumption` has a sorry-free proof, so the formal proof may no longer need to be marked `conditional`.

Note: This linter can be disabled with `set_option linter.style.conditional_formal_proof false`
-/
#guard_msgs in
/-- A proof still marked conditional on something now proved. -/
@[category research solved,
  conditional formal_proof using lean4 at "https://github.com/example/no-longer-conditional"
    assuming a_proved_assumption]
theorem conditional_on_a_proved_assumption : 6 + 6 = 12 := by
  rfl

end FormalProofLinter
