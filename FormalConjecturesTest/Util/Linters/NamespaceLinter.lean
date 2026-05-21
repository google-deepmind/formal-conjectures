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

import FormalConjectures.Util.Linters.NamespaceLinter

-- Declarations in a namespace should not trigger the linter
namespace Foo

#guard_msgs in
theorem test_in_namespace : 1 + 1 = 2 := by
  rfl

#guard_msgs in
def test_def : Nat := 42

end Foo

-- Nested namespaces should work fine
namespace Bar.Baz

#guard_msgs in
theorem test_nested_namespace : 1 + 1 = 2 := by
  rfl

end Bar.Baz

-- Declarations at the root level should trigger the linter
/--
warning: The declaration 'test_no_namespace' is not inside a namespace. All declarations should be placed within a namespace.

Note: This linter can be disabled with `set_option linter.style.namespace false`
-/
#guard_msgs in
theorem test_no_namespace : 1 + 1 = 2 := by
  rfl

/--
warning: The declaration 'test_def_no_namespace' is not inside a namespace. All declarations should be placed within a namespace.

Note: This linter can be disabled with `set_option linter.style.namespace false`
-/
#guard_msgs in
def test_def_no_namespace : Nat := 42

-- The linter can be disabled
set_option linter.style.namespace false in
#guard_msgs in
theorem test_disabled : 1 + 1 = 2 := by
  rfl
