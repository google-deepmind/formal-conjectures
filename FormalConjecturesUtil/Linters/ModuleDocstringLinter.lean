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
module

public import Lean

/-!
# The Module Docstring Linter

This file implements a linter that enforces module docstring hygiene:

1. **Missing module docstring**: warns when a file has no `/-! ... -/`
   block at all (detected on the first non-`moduleDoc` command).
2. **Duplicate module docstrings**: warns when a file has more than one
   `/-! ... -/` block (subsequent blocks should be regular `/- ... -/`
   comments).
-/

public section

open Lean Elab Meta Command Linter

register_option linter.style.moduleDocstring : Bool := {
  defValue := true
  descr := "enable the module docstring linter"
}

namespace ModuleDocstringLinter

/-- Files whose first non-`moduleDoc` command has already been
processed (so we emit the "missing" warning at most once). -/
private initialize checkedForDoc :
    IO.Ref (Std.HashSet String) ← IO.mkRef {}

/-- The module docstring linter checks two things:
- A file that has **no** `/-! ... -/` block gets a warning on its
  first non-`moduleDoc` command.
- A file that has **more than one** `/-! ... -/` block gets a
  warning on each extra block. -/
def moduleDocstringLinter : Linter where run := withSetOptionIn fun stx ↦ do
  let fileName ← getFileName
  let env ← getEnv
  if stx.getKind == ``Lean.Parser.Command.moduleDoc then
    -- Duplicate check
    let numDocs := (getMainModuleDoc env).size + (getVersoModuleDocs env).snippets.size
    if numDocs > 1 then
      Lean.Linter.logLintIf linter.style.moduleDocstring stx
        "This file has more than one module docstring \
         (`/-! ... -/`). Only the first one is treated as \
         module documentation; convert additional ones to \
         regular comments (`/- ... -/`)."
  else
    -- Missing check: on the first non-moduleDoc command,
    -- warn if no moduleDoc has been seen for this file.
    let checked ← checkedForDoc.get
    unless checked.contains fileName do
      checkedForDoc.modify (·.insert fileName)
      let hasDoc := !(getMainModuleDoc env).isEmpty || !(getVersoModuleDocs env).snippets.isEmpty
      unless hasDoc do
        Lean.Linter.logLintIf linter.style.moduleDocstring stx
          "This file has no module docstring (`/-! ... -/`). \
           Add one after the imports to document the file."

initialize addLinter moduleDocstringLinter

end ModuleDocstringLinter
