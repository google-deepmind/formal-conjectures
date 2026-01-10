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
import FormalConjectures.Util.Attributes

set_option warn.sorry false

/--
warning: If a problem has a sorry-free proof, it should not be categorised as `open`.
-/
#guard_msgs in
@[category research open]
theorem test_failure : 1 = 1 := by
  rfl

#guard_msgs in
@[category research open]
theorem test_success_1 : 1 = 1 :=
  sorry

#guard_msgs in
@[category research open]
theorem test_success_2 : 1 = 1 := by
  rotate_left
  sorry

#guard_msgs in
@[category research open]
theorem test_success_3 : 1 = 1 := by
  rotate_left
  sorry

#guard_msgs in
@[category high_school]
theorem test_ignore_other_categories : 1 = 1 :=
  rfl
