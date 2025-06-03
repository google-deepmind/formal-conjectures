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
any way to replace answer(sorry): it requires evaluation of mathematical meaning,
which is a job for human mathematicians, not Lean alone.
-/
namespace Google

open Lean Elab Term

/-- Indicates where the answer is in a problem statement. -/
@[term_elab answer]
def answerElab : TermElab := fun stx expectedType? => do
  match stx with
  | `(answer($a:term)) => do
    mkSaveInfoAnnotation <$> postponeElabTerm (← `(by exact $a)) expectedType?
  | _ => Elab.throwUnsupportedSyntax

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
