/-
Copyright 2025 The Formal Conjectures Authors.

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

import Lean.Elab
import Lean.Meta.Basic
import FormalConjectures.Util.Answer.Syntax
import Batteries.Lean.Expr

/-!
# The `answer( )` elaborator

This file provides syntax for marking up answers in a problem statement.

Note: certain problems also providing an answer, and can be formalised
using `answer(sorry)` as a placeholder. While providing a proof simply requires
finding any way to replace `:= sorry`, providing an answer is not just finding
any way to replace `answer(sorry)`: it requires evaluation of mathematical meaning,
which is a job for human mathematicians, not Lean alone.
-/
namespace Google

universe u

open Lean Elab Term

/-- A type that captures the current setting for the `answer()` elaborator. -/
inductive AnswerSetting
  /--Default mode: `answer(sorry)` defaults to `True` when `sorry` has type `Prop`. -/
  | alwaysTrue
  /-- Default mode for `answer(foo)`: just postpones elaboration. -/
  | postpone
  /-- Elaborate `answer(foo)` by creating an auxiliary definition with value `foo`.
    **For now, this is experimental** -/
  | withAuxiliary
deriving Inhabited, ToJson, BEq

instance : ToString AnswerSetting where
  toString
    | .postpone => "postpone"
    | .withAuxiliary  => "with_auxiliary"
    | .alwaysTrue => "always_true"

instance : KVMap.Value AnswerSetting where
  toDataValue := DataValue.ofString ∘ ToString.toString
  ofDataValue?
    | .ofString "postpone" => some .postpone
    | .ofString "with_auxiliary" => some .withAuxiliary
    | .ofString "always_true" => some .alwaysTrue
    | _ => none

register_option google.answer : AnswerSetting := {
  defValue := .alwaysTrue
  descr := "Modifies the behaviour of the answer() elaborator."
}

def mkAnswerAnnotation (e : Expr) : Expr := mkAnnotation `answer e

def elabTermAndAnnotate (stx : TSyntax `term) (expectedType? : Option Expr)
    (postpone : Bool := false) :=
  mkAnswerAnnotation <$> do
    if postpone then
      postponeElabTerm (← `(by exact $stx)) expectedType?
    else
      elabTerm stx expectedType?

/-- Indicates where the answer is in a problem statement. -/
@[term_elab answer]
def answerElab : TermElab := fun stx expectedType? => do
  match stx with
  | `(answer($a:term)) =>
    match (← getOptions).get? `google.answer |>.get! with
    |  AnswerSetting.postpone => elabTermAndAnnotate a expectedType? true
    | .withAuxiliary =>
      let expr ← elabTermAndAnnotate a expectedType?
      let exprType ← (Meta.inferType expr) >>= instantiateMVars
      if exprType.hasExprMVar then throwPostpone
      let some declName := (← read).declName?
        | throwError "Failed to find the name of the declaration"
      let answerName : Name := declName.str "_answer"
      let levelParams : List Name := []
      let answerAuxiliaryDecl : DefinitionVal := {
        name := answerName
        -- TODO(Paul-Lez): For now, let's ignore universes to get a working v0, but fix it later?
        levelParams := []
        type := exprType
        value := expr
        hints := .abbrev
        safety := .safe
      }
      addDecl (.defnDecl answerAuxiliaryDecl) true
      return mkAnswerAnnotation (.const answerName [])
    | .alwaysTrue =>
      -- If the answer is a `sorry` of type `Prop` then default to `True` in this setting
      if expectedType? == some (Expr.sort .zero) && a == (← `(term| sorry)) then
        return .const `True []
      else
        elabTermAndAnnotate a expectedType?
  | _ => Elab.throwUnsupportedSyntax

-- TODO: add delaborator (for the auxiliary declaration mode!)

open InfoTree

/-- An answer: a term, and the context in which it was elaborated -/
structure AnswerInfo where
  ctx : Elab.ContextInfo
  term : Elab.TermInfo

/-- Print an answer -/
def AnswerInfo.format (a : AnswerInfo) : Elab.Term.TermElabM MessageData :=
  Meta.withMCtx a.ctx.mctx <| Meta.withLCtx a.term.lctx {} do
    let t ← Meta.inferType a.term.expr
    let m ← Meta.mkFreshExprMVar t
    addMessageContextFull m!"{a.term.expr} in context:{indentD m.mvarId!}"

/-- Find answers by inspecting an `InfoTree` -/
partial def getAnswers {m} [Monad m] (i : InfoTree) : m (Array AnswerInfo) :=
  go none i
where go : _ → InfoTree → _
  | ctx?, context ctx t => go (ctx.mergeIntoOuter? ctx?) t
  | some ctx, node i cs => do
    let ctx := i.updateContext? ctx
    if let .ofTermInfo t := i then
      if t.elaborator == ``answerElab then
        if let .some ctx := ctx then
          return #[⟨ctx, t⟩]
    return (← cs.mapM (go <| i.updateContext? ctx)).toArray.flatten
  | _, _ => pure #[]

end Google
