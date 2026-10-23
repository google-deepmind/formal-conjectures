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

#guard_msgs in
/-- A statement with a formal proof that has a proper `by sorry` proof. -/
@[category research solved,
  formal_proof using lean4 at "https://example.com"]
theorem a_formal_proof_with_sorry : 2 + 2 = 4 := by
  sorry

/--
warning: A statement with a `formal_proof` annotation must be proved exactly `by sorry` in this repository (unless it has conditionals). Proofs should live in their own repository or branch.

Note: This linter can be disabled with `set_option linter.style.conditional_formal_proof false`
-/
#guard_msgs in
/-- A statement with a formal proof that does NOT have exactly `sorry` (it is proved). -/
@[category research solved,
  formal_proof using lean4 at "https://example.com"]
theorem a_formal_proof_with_rfl : 2 + 2 = 4 := by
  rfl

/--
warning: A statement with a `formal_proof` annotation must be proved exactly `by sorry` in this repository (unless it has conditionals). Proofs should live in their own repository or branch.

Note: This linter can be disabled with `set_option linter.style.conditional_formal_proof false`
-/
#guard_msgs in
/-- A statement with a formal proof that does NOT have exactly `sorry` (it has induction then sorry). -/
@[category research solved,
  formal_proof using lean4 at "https://example.com"]
theorem a_formal_proof_with_partial_proof (n : Nat) : n = n := by
  cases n <;> sorry

/--
warning: A statement with a `formal_proof` annotation must be proved exactly `by sorry` in this repository (unless it has conditionals). Proofs should live in their own repository or branch.

Note: This linter can be disabled with `set_option linter.style.conditional_formal_proof false`
-/
#guard_msgs in
/-- One unconditional proof among several makes the exact-sorry rule apply. -/
@[category research solved,
  conditional formal_proof using lean4 at "https://example.com/conditional"
    assuming FormalProofLinter.an_open_assumption,
  formal_proof using other_system at "https://example.com/unconditional"]
theorem mixed_conditional_and_unconditional_proofs : 8 + 8 = 16 := by
  rfl

/--
warning: The assumed hypothesis `FormalProofLinter.a_proved_assumption` has a sorry-free proof, so the formal proof may no longer need to be marked `conditional`.

Note: This linter can be disabled with `set_option linter.style.conditional_formal_proof false`
-/
#guard_msgs in
/-- Every proof condition is inspected, with duplicate conditions reported once. -/
@[category research solved,
  conditional formal_proof using lean4 at "https://example.com/first"
    assuming FormalProofLinter.a_proved_assumption,
  conditional formal_proof using other_system at "https://example.com/second"
    assuming FormalProofLinter.a_proved_assumption]
theorem multiple_conditional_proofs : 10 + 10 = 20 := by
  rfl
