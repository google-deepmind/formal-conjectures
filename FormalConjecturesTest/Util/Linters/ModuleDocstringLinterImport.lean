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

import FormalConjecturesTest.Util.Linters.ModuleDocstringLinter

-- The imported file contains multiple module docstrings, but per-file
-- tracking means the first module docstring in *this* file should not
-- trigger a warning.
#guard_msgs in
/-! This is the first module docstring in this file; it should not trigger a warning. -/

-- Enable the linter for the rest of this file.
set_option linter.style.moduleDocstring true

-- A second `/-! ... -/` should trigger the duplicate warning.
/--
warning: This file has more than one module docstring (`/-! ... -/`). Only the first one is treated as module documentation; convert additional ones to regular comments (`/- ... -/`).

Note: This linter can be disabled with `set_option linter.style.moduleDocstring false`
-/
#guard_msgs in
/-! This is a second module docstring and should trigger a warning. -/
