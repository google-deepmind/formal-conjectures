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

/-! # Helpers shared by the linters -/

public meta section

open Lean Elab Command

namespace FormalConjectures.Linter

/-- The full name of the declaration a `theorem`, `lemma`, or `def` command declares, computed
from its modifiers and `declId` the way `mkDeclName` does.

`Lean.Elab.expandDeclId` is the natural thing to reach for here, but it calls `applyVisibility`,
which throws `already been declared` once the declaration exists, and a linter runs after that.
`expandDeclIdCore` is the pure part of it: it accepts the bare-identifier form of `declId`, which
indexing `declId[0]` does not. The `_root_` and `private` cases are then handled the way
`mkDeclName` handles them. -/
def resolveDeclName (mods : TSyntax ``Parser.Command.declModifiers) (declId : Syntax) :
    CommandElabM Name := do
  let modifiers ← elabModifiers mods
  let (shortName, _) := Lean.Elab.expandDeclIdCore declId
  let declName ←
    if (`_root_).isPrefixOf shortName then
      pure <| shortName.replacePrefix `_root_ .anonymous
    else
      pure <| (← getCurrNamespace) ++ shortName
  let env ← getEnv
  return if modifiers.isPrivate then mkPrivateName env declName else declName

end FormalConjectures.Linter
