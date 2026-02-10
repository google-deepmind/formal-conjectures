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

import Mathlib.Tactic.DeclarationNames

/-! # The Namespace Linter

The `namespaceLinter` is a linter to aid with formatting contributions to
the Formal Conjectures repository by ensuring that all declarations are
placed within a namespace.
-/

namespace NamespaceLinter

open Lean Parser Elab Command Meta Linter

/--
The `namespace` linter is set on by default. It emits a warning on any declaration
that is not inside a namespace (i.e., declarations at the root level).

For instance, `theorem foo` would trigger a warning, while `Nat.foo` would not.

This helps maintain organization and avoid polluting the global namespace.
-/
register_option linter.style.namespace : Bool := {
  defValue := true
  descr := "enable the namespace linter"
}

/-- The namespace linter checks that every declaration is inside a namespace. -/
def namespaceLinter : Linter where run := withSetOptionIn fun stx ↦ do
  if getLinterValue linter.style.namespace (← getLinterOptions) then
    for id in (← Mathlib.Linter.getNamesFrom (stx.getPos?.getD default)) do
      let declName := id.getId
      if declName.hasMacroScopes then continue
      let nm := declName.components
      -- If the declaration has only one component, it's not in a namespace
      if nm.length == 1 then
        Linter.logLint linter.style.namespace id
          m!"The declaration '{declName}' is not inside a namespace. All declarations should be placed within a namespace."

initialize addLinter namespaceLinter

end NamespaceLinter
