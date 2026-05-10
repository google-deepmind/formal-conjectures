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

public import FormalConjectures.Util.Attributes.Basic
public import Mathlib.Tactic.Lemma

/-! # The Category Docstring Linter

The `CategoryDocstringLinter` ensures that declarations tagged as
`@[category research open]`, `@[category research solved]`, or `@[category textbook]` have a docstring.
-/

public meta section

open Lean Elab Meta Linter Command Parser Term ProblemAttributes

register_option linter.style.category_docstring : Bool := {
  defValue := true
  descr := "enable the research category docstring style linter"
}

-- FIXME: False positive
set_option linter.style.docString.empty false

namespace CategoryDocstringLinter

/-- Extract the `category` attributes from a declaration's modifiers. -/
def toCategorySyntax
    (stx : TSyntax ``Command.declModifiers) :
    CommandElabM (Array <| TSyntax ``attrInstance) := do
  match stx with
  | `(declModifiers| $(_)? @[$[$atts],*] $(_)? $(_)? $(_)? $(_)?) =>
    atts.filterM fun att ↦ do
      match att with
      | `(attrInstance | category $_) => return true
      | _ => return false
  | _ => return #[]

/-- Extract the categories from a declaration's modifiers. -/
def toCategories
    (stx : TSyntax ``Command.declModifiers) :
    CommandElabM (Array ProblemAttributes.Category) := do
  let cats ← toCategorySyntax stx
  cats.mapM fun
    | `(attrInstance | category $s) => liftCoreM <| ProblemAttributes.Syntax.toCategory s
    | _ => throwUnsupportedSyntax

/-- Whether the given category requires a docstring. -/
def categoryNeedsDocstring : ProblemAttributes.Category → Bool
  | .research .open | .research .solved | .textbook => true
  | _ => false

/-- Whether the declaration modifiers contain a docstring. -/
def hasDocstring (stx : TSyntax ``Command.declModifiers) : Bool :=
  let docstring := stx.raw[0]!
  !(Syntax.getAtomVal (docstring[0]![1]!)).isEmpty

/-- The linter checking for docstrings on research statements. -/
def categoryDocstringLinter : Linter where
  run := withSetOptionIn fun stx => do
    match stx with
    | `(command| $mods:declModifiers theorem $name:declId $sig:declSig $val:declVal)
    | `(command| $mods:declModifiers lemma $name:declId $sig:declSig $val:declVal) =>
      let cats ← toCategories mods
      if cats.any categoryNeedsDocstring && !hasDocstring mods then
        logLintIf linter.style.category_docstring name
          "Declarations tagged `@[category research open]`, `@[category research solved]`, or `@[category textbook]` must have a docstring."
    | _ => return

initialize do
  addLinter categoryDocstringLinter

end CategoryDocstringLinter
