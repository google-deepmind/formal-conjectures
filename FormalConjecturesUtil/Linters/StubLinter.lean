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

public meta import Mathlib.Tactic.DeclarationNames
public import Mathlib.Tactic.Linter.Header

/-! # The Stub Linter

The `StubLinter` ensures that no stubs, placeholder definitions (e.g. `opaque`, `def ... := sorry`),
or new axioms are introduced in the repository.
-/

public meta section

open Lean Elab Meta Linter Command Parser Term

register_option linter.style.stubs : Bool := {
  defValue := false
  descr := "enable the linter to forbid stubs, placeholder definitions, and axioms"
}

namespace StubLinter

/-- Checks whether a syntax node contains `sorry`, `admit`, or `sorryAx`. -/
def hasSorry (stx : Syntax) : Bool :=
  stx.find? (fun s =>
    s.isOfKind ``Lean.Parser.Term.sorry ||
    s.isOfKind ``Lean.Parser.Tactic.tacticSorry ||
    s.isOfKind ``Lean.Parser.Tactic.tacticAdmit ||
    (s.isIdent && (s.getId == `sorry || s.getId == `sorryAx ||
                   s.getId.eraseMacroScopes == `sorry || s.getId.eraseMacroScopes == `sorryAx))
  ) != none

/-- The `declId` of a declaration, if it has one: an `instance` may be anonymous. -/
def declId? (decl : Syntax) : Option Syntax :=
  decl.getArgs.findSome? fun arg =>
    if arg.isOfKind ``Lean.Parser.Command.declId then some arg
    -- `instance` wraps its `declId` in an `optional`, hence in a null node.
    else if arg.isOfKind nullKind then arg.getArgs.find? (·.isOfKind ``Lean.Parser.Command.declId)
    else none

/-- The names introduced by the declaration command `stx`, whose declaration node is `decl`.
That is the single name given by its `declId`, resolved the way `CategoryLinter` resolves it, or,
for an anonymous `instance`, the auto-generated names recorded at or after the position of `stx`. -/
def declNames (stx decl : Syntax) : CommandElabM (Array Name) := do
  let some declId := declId? decl
    | let some pos := stx.getPos? | return #[]
      return (← Mathlib.Linter.getNamesFrom pos).map (·.getId)
  let modifiers ← elabModifiers ⟨stx[0]⟩
  let (shortName, _) := Lean.Elab.expandDeclIdCore declId
  let currNamespace ← getCurrNamespace
  let env ← getEnv
  let declName :=
    if (`_root_).isPrefixOf shortName then shortName.replacePrefix `_root_ .anonymous
    else currNamespace ++ shortName
  return #[if modifiers.isPrivate then mkPrivateName env declName else declName]

/-- Whether every declaration in `declNames` is `Prop`-valued, and there is at least one.

A `Prop`-valued declaration whose proof is `sorry` is a statement waiting to be proved, exactly
like a `theorem`, rather than a placeholder definition. This is what lets a `Prop`-valued
`instance`, such as `instance mordell_weil : Module.Finite ℤ E.Point := by sorry`, state a
conjecture. -/
def isPropValued (declNames : Array Name) : CommandElabM Bool := do
  let declNames := declNames.filter (!·.isInternal)
  if declNames.isEmpty then return false
  let env ← getEnv
  liftTermElabM <| declNames.allM fun declName => do
    -- `findAsync?` rather than `find?` so that this also sees a declaration of the file being
    -- elaborated; `toConstantVal` only needs the signature, which is available right away.
    let some info := env.findAsync? declName | return false
    isProp info.toConstantVal.type

/-- Checks a declaration command for stubs, placeholder definitions, and axioms. -/
def checkDecl (stx : Syntax) : CommandElabM Unit := do
  if stx.getKind == ``Lean.Parser.Command.declaration then
    let decl := stx[1]
    let kind := decl.getKind
    if kind == ``Lean.Parser.Command.opaque then
      logLintIf linter.style.stubs stx
        "Placeholder definitions (e.g., `opaque foo : Type*`) are not allowed."
    else if kind == ``Lean.Parser.Command.axiom then
      logLintIf linter.style.stubs stx
        "New axioms (e.g., `axiom foo : ...`) are not allowed."
    else if kind == ``Lean.Parser.Command.definition ||
            kind == ``Lean.Parser.Command.abbrev ||
            kind == ``Lean.Parser.Command.instance ||
            kind == ``Lean.Parser.Command.structure then
      if hasSorry decl && !(← isPropValued (← declNames stx decl)) then
        logLintIf linter.style.stubs stx
          "Placeholder definitions (e.g., `def foo : Type := sorry`) are not allowed."

/-- The stub linter checks that no `opaque`, `axiom`, or `def ... := sorry` definitions are present. -/
def stubLinter : Linter where
  run := withSetOptionIn fun stx => do
    if stx.getKind == ``Lean.Parser.Command.mutual then
      for arg in stx[1].getArgs do
        checkDecl arg
    else
      checkDecl stx

initialize do
  addLinter stubLinter

end StubLinter
