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

import Lean

/-!
# The Module Docstring Linter

This file implements a linter that checks that every file has at most one
module docstring (a `/-! ... -/` block). If more than one is present, the
extra ones are flagged with a warning suggesting they be converted to regular
multiline comments (`/- ... -/`).
-/

open Lean Elab Meta Command Linter

register_option linter.style.moduleDocstring : Bool := {
  defValue := true
  descr := "enable the module docstring count linter"
}

namespace ModuleDocstringLinter

/-- Tracks which files have already had their first module docstring. -/
private initialize seenModuleDoc : IO.Ref (Array String) ← IO.mkRef #[]

/-- The module docstring linter warns when a file contains more than one
`/-! ... -/` block. The first such block is the module docstring; all
subsequent ones should be regular comments (`/- ... -/`). -/
def moduleDocstringLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless stx.getKind == ``Lean.Parser.Command.moduleDoc do return
  let fileName ← getFileName
  let seen ← seenModuleDoc.get
  if seen.contains fileName then
    Lean.Linter.logLintIf linter.style.moduleDocstring stx
      "This file has more than one module docstring (`/-! ... -/`). \
       Only the first one is treated as module documentation; \
       convert additional ones to regular comments (`/- ... -/`)."
  else
    seenModuleDoc.modify (·.push fileName)

initialize addLinter moduleDocstringLinter

end ModuleDocstringLinter
