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

/-- Whether an `import` syntax node carries a modifier of the given kind, such as `meta`. -/
def hasImportModifier (kind : SyntaxNodeKind) (stx : Syntax) : Bool :=
  -- a modifier is parsed as an `optional` node wrapping a node of the given kind
  stx.getArgs.any fun arg ↦ arg.isOfKind kind || arg.getArgs.any (·.isOfKind kind)

/-- Whether an `import` syntax node carries the `meta` modifier. -/
def isMetaImport (stx : Syntax) : Bool := hasImportModifier ``Lean.Parser.Module.meta stx

/-- Whether an `import` syntax node carries the `public` modifier. -/
def isPublicImport (stx : Syntax) : Bool := hasImportModifier ``Lean.Parser.Module.public stx

/-- An `import` of a parsed header. -/
structure HeaderImport where
  /-- The identifier of the imported module. -/
  id : Syntax
  /-- Whether the import carries the `public` modifier. -/
  isPublic : Bool
  /-- Whether the import carries the `meta` modifier. -/
  isMeta : Bool

/--
Collects every `import` of a parsed header, with its modifiers. This mirrors
`Mathlib.Linter.getImportIds`, which discards the modifiers.
-/
partial def getImports (stx : Syntax) : Array HeaderImport :=
  let rest := (stx.getArgs.map getImports).flatten
  if stx.isOfKind `Lean.Parser.Module.import then
    -- The module name is the last identifier in the import node arguments
    match stx.getArgs.filter (·.isIdent) |>.back? with
    | some n => rest.push { id := n, isPublic := isPublicImport stx, isMeta := isMetaImport stx }
    | none => rest
  else
    rest

/--
Checks a parsed header against the Formal Conjectures import rules. `meta` imports are exempt
from the rules on direct `Mathlib` and `FormalConjecturesForMathlib` imports.
-/
def checkImports (header : HeaderSyntax) (isFormalConjecturesModule : Bool := true)
    (firstCmdStx : Syntax := .missing) : CommandElabM Unit := do
  let imports := getImports header
  for imp in imports do
    let modName := imp.id.getId
    if imp.isMeta then
      if modName ∈ [`FormalConjecturesUtil, `FormalConjecturesForMathlib, `Mathlib] then
        Linter.logLintIf linter.style.imports imp.id
          m!"'meta import {modName}' loads the compiled code of the whole library. \
             Instead, 'meta import' only the module defining the declaration that is evaluated \
             (for example by 'native_decide')."
      continue
    if modName == `Mathlib || modName.getRoot == `Mathlib then
      Linter.logLintIf linter.style.imports imp.id
        m!"Direct imports from 'Mathlib' (such as '{modName}') are disallowed in 'FormalConjectures'. \
           Use 'import FormalConjecturesUtil' instead."
    if modName == `FormalConjecturesForMathlib || modName.getRoot == `FormalConjecturesForMathlib then
      Linter.logLintIf linter.style.imports imp.id
        m!"Direct imports from 'FormalConjecturesForMathlib' (such as '{modName}') are disallowed in 'FormalConjectures'. \
           Use 'import FormalConjecturesUtil' instead."

  if isFormalConjecturesModule then
    let targetStx := imports[0]?.map (·.id) |>.getD firstCmdStx
    unless header.isModule do
      Linter.logLintIf linter.style.imports targetStx
        "Files in 'FormalConjectures' must be modules. Add 'module' before the imports, use \
         'public import FormalConjecturesUtil', and add '@[expose] public section' after the \
         module docstring."
    match imports.find? fun imp ↦ !imp.isMeta && imp.id.getId == `FormalConjecturesUtil with
    | none =>
      Linter.logLintIf linter.style.imports targetStx
        "Files in 'FormalConjectures' must import 'FormalConjecturesUtil'."
    | some util =>
      if header.isModule && !util.isPublic then
        Linter.logLintIf linter.style.imports util.id
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
