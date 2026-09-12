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

public import FormalConjecturesUtil.Attributes.Basic
public import FormalConjecturesUtil.Answer.Syntax
public import Mathlib.Tactic.Lemma

/-! # The Category Answer Linter

The `CategoryAnswerLinter` ensures that declarations tagged `@[category research solved]`
do not leave `answer(sorry)` in their statement: once a problem is solved, the answer should
be filled in explicitly, e.g. `answer(True)`.

The check is syntactic. Under the default `google.answer` setting, `answer(sorry)` at `Prop`
elaborates to a bare `True` carrying no annotation, so the placeholder is no longer visible
in the elaborated term.

A statement that deliberately keeps `answer(sorry)` (for instance because the problem is
independent of ZFC, or because the answer is a constant that is not known explicitly) can opt
out with `set_option linter.style.category_answer false in`.
-/

public meta section

open Lean Elab Meta Linter Command Parser Term ProblemAttributes

register_option linter.style.category_answer : Bool := {
  defValue := false
  descr := "enable the linter checking for `answer(sorry)` in solved statements"
}

namespace CategoryAnswerLinter

/-- Whether `stx` contains a `sorry` anywhere. -/
partial def containsSorry (stx : Syntax) : Bool :=
  stx.isOfKind ``Lean.Parser.Term.sorry || stx.getArgs.any containsSorry

/-- The `answer(..)` nodes in `stx` whose answer is still a `sorry`. -/
partial def answerSorries (stx : Syntax) : Array Syntax :=
  let nested := stx.getArgs.foldl (init := #[]) fun acc arg => acc ++ answerSorries arg
  if stx.isOfKind ``Google.answer && containsSorry stx[1] then nested.push stx else nested

/-- Whether the given category is `research solved`. -/
def categoryNeedsAnswer (cat : ProblemAttributes.Category) : Bool :=
  cat == .research .solved

/-- The linter checking that solved statements do not use `answer(sorry)`. -/
def categoryAnswerLinter : Linter where
  run := withSetOptionIn fun stx => do
    match stx with
    | `(command| $mods:declModifiers theorem $_:declId $sig:declSig $_:declVal)
    | `(command| $mods:declModifiers lemma $_:declId $sig:declSig $_:declVal) =>
      let cats ← ProblemAttributes.toCategories mods
      if cats.any categoryNeedsAnswer then
        for answer in answerSorries sig.raw do
          logLintIf linter.style.category_answer answer
            "Declarations tagged `@[category research solved]` should not use `answer(sorry)`: \
            the answer should be filled in explicitly, e.g. `answer(True)`."
    | _ => return

initialize do
  addLinter categoryAnswerLinter

end CategoryAnswerLinter
