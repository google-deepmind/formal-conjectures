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

import FormalConjectures.Util.Linters.ModuleDocstringLinter

/-!
# Tests for the module docstring linter

This file tests that the module docstring linter correctly flags files with
more than one `/-! ... -/` block, and does not flag the first one.
-/

-- The module docstring above is the first (and only expected) one, so no warning.

-- A second module docstring should trigger the linter.
/--
warning: This file has more than one module docstring (`/-! ... -/`). Only the first one is treated as module documentation; convert additional ones to regular comments (`/- ... -/`).

Note: This linter can be disabled with `set_option linter.style.moduleDocstring false`
-/
#guard_msgs in
/-! This is a second module docstring and should trigger a warning. -/

-- A third module docstring also triggers the linter.
/--
warning: This file has more than one module docstring (`/-! ... -/`). Only the first one is treated as module documentation; convert additional ones to regular comments (`/- ... -/`).

Note: This linter can be disabled with `set_option linter.style.moduleDocstring false`
-/
#guard_msgs in
/-! This is yet another module docstring. -/

-- The linter can be disabled with set_option.
set_option linter.style.moduleDocstring false in
#guard_msgs in
/-! This module docstring does not trigger a warning because the linter is disabled. -/
