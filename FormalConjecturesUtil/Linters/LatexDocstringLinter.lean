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
public meta import Init.Data.String.Legacy
public meta import Lean.Linter.Basic

/-! # The Docstring Markup Linter

The `LatexDocstringLinter` checks markup that affects generated documentation. It ensures that
docstrings use `$ $` or `$$ $$` for mathematics and use inline Markdown links for URLs.
-/

public meta section

open Lean Elab Meta Linter Command Parser

register_option linter.style.latex_docstring : Bool := {
  defValue := true
  descr := "enable the docstring markup style linter"
}

namespace LatexDocstringLinter

def containsLatex (s : String) : Bool :=
  (s.splitOn "\\[").length > 1 || (s.splitOn "\\]").length > 1 ||
  (s.splitOn "\\(").length > 1 || (s.splitOn "\\)").length > 1

def containsLegacyUrlLink (s : String) : Bool :=
  (s.splitOn "][http://").length > 1 || (s.splitOn "][https://").length > 1

def getDocstringText (stx : TSyntax ``Command.declModifiers) : String :=
  let docstring := stx.raw[0]!
  Syntax.getAtomVal (docstring[0]![1]!)

def lintDocstring (location : Syntax) (text : String) : CommandElabM Unit := do
  if containsLatex text then
    logLintIf linter.style.latex_docstring location
      "Docstrings should use `$ $` or `$$ $$` for math formulas instead of `\\[ \\]` or `\\( \\)`."
  if containsLegacyUrlLink text then
    logLintIf linter.style.latex_docstring location
      "Docstring URLs should use `[label](https://...)`, not `[label][https://...]`."

/-- The linter checking markup in docstrings. -/
def latexDocstringLinter : Linter where
  run := withSetOptionIn fun stx => do
    if stx.getKind == ``Lean.Parser.Command.moduleDoc then
      let text := Syntax.getAtomVal stx[1]!
      lintDocstring stx text
      return
    match stx with
    | `(command| $mods:declModifiers theorem $name:declId $sig:declSig $val:declVal) =>
      let text := getDocstringText mods
      if text != "" then
        lintDocstring name text
    | _ => return

initialize do
  addLinter latexDocstringLinter

end LatexDocstringLinter
