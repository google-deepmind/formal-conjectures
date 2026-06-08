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

This file tests that the module docstring linter:
1. Does not flag the first `/-! ... -/` block.
2. Flags files with more than one `/-! ... -/` block.
3. Can be disabled with `set_option`.

The "missing module docstring" warning is tested in
`ModuleDocstringLinterMissing.lean`.
-/

-- Enable the linter for this test file
-- (it is off by default; enabled via lakefile for FormalConjectures).
set_option linter.style.moduleDocstring true

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
