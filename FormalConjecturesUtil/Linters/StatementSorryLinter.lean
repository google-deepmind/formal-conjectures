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

public import FormalConjecturesUtil.Linters.Util
public import Mathlib.Tactic.Lemma

/-! # The Statement Sorry Linter

The `StatementSorryLinter` ensures that the statement of a theorem does not depend on `sorry`.
The only placeholder a statement may use is the unknown `<theorem>.answer` of a value question,
which is a definition left as `sorry` until the question is answered.

`StubLinter` rejects a `def ... := sorry` where it is written. This linter catches the indirect
cases: a definition whose body uses a theorem proved by `sorry`, say through `Nat.find` or
`Classical.choose`, or a definition built from another placeholder.

The search follows constants through their values, but only inside this repository's modules:
Mathlib and core are `sorry`-free, so they are not traversed.
-/

public meta section

open Lean Elab Meta Linter Command Parser Term

register_option linter.style.statement_sorry : Bool := {
  defValue := false
  descr := "enable the linter checking that a statement does not depend on `sorry`"
}

namespace StatementSorryLinter

/-- Whether constants of module `mod` are followed by the search. The current module has no
name in `env.header.moduleNames`, so `none` is followed too. -/
def followsModule (env : Environment) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | none => true
  | some idx => (`FormalConjectures).isPrefixOf env.header.moduleNames[idx]! ||
      (`FormalConjecturesForMathlib).isPrefixOf env.header.moduleNames[idx]!

/-- The results of `sorrySource` found so far in this process, since the same constants come up
in every statement of a file. -/
initialize sorrySourceCache : IO.Ref (Std.HashMap Name (Option Name)) ← IO.mkRef {}

/-- The first constant on a path from `root` to `sorryAx`, following definitions and proofs
inside this repository, but not the unknown `answer` of a value question. `none` if `root` does
not depend on `sorry` in this way. The constant returned is `sorryAx` itself if `root` uses it
directly. -/
partial def sorrySource (env : Environment) (root : Name) : IO (Option Name) := do
  if let some r := (← sorrySourceCache.get)[root]? then return r
  let r ← go root
  sorrySourceCache.modify (·.insert root r)
  return r
where
  go (c : Name) : IO (Option Name) := do
    if c == ``sorryAx then return some c
    if c.getString! == "answer" then return none
    unless followsModule env c do return none
    let some info := env.find? c | return none
    let used := info.type.getUsedConstants ++
      ((info.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
    for d in used do
      if d == ``sorryAx then return some c
      if let some _ ← sorrySource env d then return some c
    return none

/-- Warns when the statement of `declName` depends on `sorry` other than through an `answer`. -/
def checkStatementSorryFree (declName : Name) (declId : Syntax) : CommandElabM Unit := do
  let env ← getEnv
  let some info := env.find? declName | return
  for c in info.type.getUsedConstants do
    if let some src ← sorrySource env c then
      if src == ``sorryAx then
        logLintIf linter.style.statement_sorry declId
          m!"The statement contains `sorry`. Only the `answer` definition of a value question \
            may be left as `sorry`."
      else
        logLintIf linter.style.statement_sorry declId
          m!"The statement depends on `sorry` through `{src}`. Only the `answer` definition of \
            a value question may be left as `sorry`."
      return

/-- The statement sorry linter checks that no statement depends on `sorry`, except through the
`answer` definition of a value question. -/
def statementSorryLinter : Linter where
  run := withSetOptionIn fun stx => do
    match stx with
    | `(command| $mods:declModifiers theorem $declId:declId $_:declSig $_:declVal)
    | `(command| $mods:declModifiers lemma $declId:declId $_:declSig $_:declVal) =>
      checkStatementSorryFree (← FormalConjectures.Linter.resolveDeclName mods declId) declId
    | _ => return

initialize do
  addLinter statementSorryLinter

end StatementSorryLinter
