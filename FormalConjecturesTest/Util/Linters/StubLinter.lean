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
# Tests for StubLinter
-/

set_option linter.style.stubs true
set_option linter.style.namespace false

/--
warning: Placeholder definitions (e.g., `opaque foo : Type*`) are not allowed.

Note: This linter can be disabled with `set_option linter.style.stubs false`
-/
#guard_msgs(warning) in
opaque MyOpaqueType : Type

/--
warning: New axioms (e.g., `axiom foo : ...`) are not allowed.

Note: This linter can be disabled with `set_option linter.style.stubs false`
-/
#guard_msgs(warning) in
axiom MyNewAxiom : 1 = 1

/--
warning: Placeholder definitions (e.g., `def foo : Type := sorry`) are not allowed.

Note: This linter can be disabled with `set_option linter.style.stubs false`
-/
#guard_msgs(warning) in
def MyDefSorry : Nat := sorry

/--
warning: Placeholder definitions (e.g., `def foo : Type := sorry`) are not allowed.

Note: This linter can be disabled with `set_option linter.style.stubs false`
-/
#guard_msgs(warning) in
def MyDefBySorry : Nat := by sorry

/--
warning: Placeholder definitions (e.g., `def foo : Type := sorry`) are not allowed.

Note: This linter can be disabled with `set_option linter.style.stubs false`
-/
#guard_msgs(warning) in
def MyDefByAdmit : Nat := by admit

/--
warning: Placeholder definitions (e.g., `def foo : Type := sorry`) are not allowed.

Note: This linter can be disabled with `set_option linter.style.stubs false`
-/
#guard_msgs(warning) in
def MyDefPattern : Nat → Nat | 0 => sorry | _ => 1

/--
warning: Placeholder definitions (e.g., `def foo : Type := sorry`) are not allowed.

Note: This linter can be disabled with `set_option linter.style.stubs false`
-/
#guard_msgs(warning) in
abbrev MyAbbrevSorry : Nat := sorry

#guard_msgs in
def MyNormalType : Type := Nat

#guard_msgs in
theorem MyTheoremWithSorry : 1 = 1 := by sorry
