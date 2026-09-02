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
      if hasSorry decl then
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
