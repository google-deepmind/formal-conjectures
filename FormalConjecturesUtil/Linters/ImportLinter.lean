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

public meta import Lean.Elab.Import
public import Mathlib.Tactic.Linter.Header

/-!
# The Import Linter

This file implements a linter that enforces import conventions in `FormalConjectures`:

1. **Disallow direct `Mathlib` and `FormalConjecturesForMathlib` imports**: Problem files in
   `FormalConjectures` must not import `Mathlib`, `Mathlib.*`, `FormalConjecturesForMathlib`,
   or any `FormalConjecturesForMathlib.*` module directly. They should use
   `import FormalConjecturesUtil` instead.
2. **Require `FormalConjecturesUtil`**: Problem files in `FormalConjectures` must
   import `FormalConjecturesUtil`.

3. **Keep `meta import`s narrow**: A `meta import` does not bring any declarations into scope;
   it only loads the compiled code of the imported module (and of its transitive imports), which
   is what `native_decide` and `#eval` need under the module system. `meta import`s are therefore
   exempt from the first rule, but they must name the module defining the evaluated declaration:
   `meta import FormalConjecturesUtil`, `meta import FormalConjecturesForMathlib` and
   `meta import Mathlib` load the compiled code of the whole library and are disallowed.
4. **Require modules**: Problem files in `FormalConjectures` must be modules, and they must import
   `FormalConjecturesUtil` with `public import`. In a module, a plain `import` is private, so the
   statements of public declarations cannot use it.
-/

public meta section

open Lean Elab Command Linter

register_option linter.style.imports : Bool := {
  defValue := false
  descr := "enable the import style linter"
}

namespace ImportLinter

/--
An `import` of a parsed header, retaining its syntax node.

TODO(v4.34.0): Replace `ImportRef`, `ImportRef.getIdent`, and `headerToImportRefs` with
`ImportGraph.Lean.headerToImportRefs` from `ImportGraph.Imports.Pretty`
(added in `leanprover-community/import-graph#133`).
-/
structure ImportRef extends Import where
  /-- The syntax node of the `import` statement. -/
  stx : TSyntax ``Parser.Module.import
deriving Repr, Inhabited, BEq

/-- Extracts the module identifier from an `ImportRef`. -/
def ImportRef.getIdent (i : ImportRef) : Ident :=
  match i.stx with
  | `(Parser.Module.import| $[public]? $[meta]? import $[all]? $n:ident) => n
  | _ => ⟨.missing⟩

/-- Collects every `import` of a parsed header, with its modifiers and syntax. -/
def headerToImportRefs (header : TSyntax ``Parser.Module.header) : Array ImportRef :=
  match header with
  | `(Parser.Module.header| $[module%$moduleTk]? $[prelude]? $imports*) =>
    imports.map fun
      | stx@`(Parser.Module.import|
          $[public%$publicTk]? $[meta%$metaTk]? import $[all%$allTk]? $n:ident) =>
        { module := n.getId
          importAll := allTk.isSome
          isExported := publicTk.isSome || moduleTk.isNone
          isMeta := metaTk.isSome
          stx := ⟨stx⟩ }
      | _ => { module := `illformedStx, stx := ⟨.missing⟩ }
  | _ => #[{ module := `illformedStx, stx := ⟨.missing⟩ }]

/--
Checks a parsed header against the Formal Conjectures import rules. `meta` imports are exempt
from the rules on direct `Mathlib` and `FormalConjecturesForMathlib` imports.
-/
def checkImports (header : HeaderSyntax) (isFormalConjecturesModule : Bool := true)
    (firstCmdStx : Syntax := .missing) : CommandElabM Unit := do
  let imports := headerToImportRefs header
  for imp in imports do
    let modName := imp.module
    if imp.isMeta then
      if modName ∈ [`FormalConjecturesUtil, `FormalConjecturesForMathlib, `Mathlib] then
        Linter.logLintIf linter.style.imports imp.getIdent
          m!"'meta import {modName}' loads the compiled code of the whole library. \
             Instead, 'meta import' only the module defining the declaration that is evaluated \
             (for example by 'native_decide')."
      continue
    if modName == `Mathlib || modName.getRoot == `Mathlib then
      Linter.logLintIf linter.style.imports imp.getIdent
        m!"Direct imports from 'Mathlib' (such as '{modName}') are disallowed in 'FormalConjectures'. \
           Use 'import FormalConjecturesUtil' instead."
    if modName == `FormalConjecturesForMathlib || modName.getRoot == `FormalConjecturesForMathlib then
      Linter.logLintIf linter.style.imports imp.getIdent
        m!"Direct imports from 'FormalConjecturesForMathlib' (such as '{modName}') are disallowed in 'FormalConjectures'. \
           Use 'import FormalConjecturesUtil' instead."

  if isFormalConjecturesModule then
    let targetStx := imports[0]?.map (·.getIdent.raw) |>.getD firstCmdStx
    unless header.isModule do
      Linter.logLintIf linter.style.imports targetStx
        "Files in 'FormalConjectures' must be modules. Add 'module' before the imports, use \
         'public import FormalConjecturesUtil', and add '@[expose] public section' after the \
         module docstring."
    match imports.find? fun imp ↦ !imp.isMeta && imp.module == `FormalConjecturesUtil with
    | none =>
      Linter.logLintIf linter.style.imports targetStx
        "Files in 'FormalConjectures' must import 'FormalConjecturesUtil'."
    | some util =>
      if !util.isExported then
        Linter.logLintIf linter.style.imports util.getIdent
          "Use 'public import FormalConjecturesUtil'. In a module, a plain 'import' is private, \
           so the statements of public declarations cannot use it."

/-- Files whose header has already been checked by this linter. -/
private initialize checkedFiles : IO.Ref (Std.HashSet String) ← IO.mkRef {}

/-- The import linter ensures that:
- Files in `FormalConjectures` do not import `Mathlib`, `Mathlib.*`, `FormalConjecturesForMathlib`, or `FormalConjecturesForMathlib.*` directly.
- Files in `FormalConjectures` import `FormalConjecturesUtil`.
- Files in `FormalConjectures` do not `meta import` a whole library (`FormalConjecturesUtil`,
  `FormalConjecturesForMathlib` or `Mathlib`).
- Files in `FormalConjectures` are modules that `public import FormalConjecturesUtil`.
-/
def importLinter : Linter where run := withSetOptionIn fun stx ↦ do
  if stx.getKind == ``Lean.Parser.Command.moduleDoc then return
  unless getLinterValue linter.style.imports (← getLinterOptions) do return
  if (← get).messages.hasErrors then return
  let fileName ← getFileName
  if fileName.endsWith "FormalConjectures/All.lean" || fileName.endsWith "All.lean" then return
  let mainModule ← getMainModule
  unless mainModule.getRoot == `FormalConjectures do return
  let checked ← checkedFiles.get
  if checked.contains fileName then return
  checkedFiles.modify (·.insert fileName)

  let fm ← getFileMap
  let (headerStx, _) ← Parser.parseHeader { inputString := fm.source, fileName := fileName, fileMap := fm }
  checkImports headerStx (isFormalConjecturesModule := true) stx

initialize addLinter importLinter

/-- A command to test import validation on a simulated header string. -/
elab "#check_imports " headerStr:str : command => do
  let s := headerStr.getString
  let fm : FileMap := { source := s, positions := #[0] }
  let (headerStx, _) ← Parser.parseHeader { inputString := s, fileName := "test.lean", fileMap := fm }
  checkImports headerStx (isFormalConjecturesModule := true) headerStr

end ImportLinter
