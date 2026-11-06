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

public import Batteries.Tactic.Lint.Basic
public import FormalConjecturesUtil.Attributes.Basic

/-! # Environment linters

Checks on finished declarations that need only the environment: the declaration name, its type
and value, and the repository's attributes. They are Batteries environment linters, so they run
on a file with `#lint`, and on the whole repository with `lake exe lint_env` after a build.

- `researchOpenSorryFree`: a `research open` problem has no `sorry`-free proof.
- `valueQuestionTag`: a statement that refers to its own unknown `<theorem>.answer` is tagged
  `question value`. The attribute checks the converse.
- `foreignAnswer`: a statement refers to no other theorem's unknown, unless it is a `test` or
  `API` statement, which may state a sanity check about one.
- `statementSorry`: a statement does not depend on `sorry` except through an `answer`
  definition. The search follows definitions, proofs, and constructors inside this repository's
  modules; Mathlib and core are `sorry`-free, so they are not traversed.

A declaration can opt out of one check with `@[nolint <linter name>]`.
-/

public meta section

open Lean Meta Batteries.Tactic.Lint ProblemAttributes

namespace FormalConjectures.EnvLinter

/-- The category of `declName`, if it carries one. -/
def categoryOf (env : Environment) (declName : Name) : Option Category :=
  (categoryExt.getState env).toArray.find? (·.declName == declName) |>.map (·.category)

/-- Whether `declName` is something a contributor wrote, as opposed to a projection of a
structure, which inherits whatever its structure depends on. -/
def isWritten (env : Environment) (declName : Name) : Bool :=
  !env.isProjectionFn declName

/-- A `research open` problem must not have a `sorry`-free proof. -/
@[env_linter] def researchOpenSorryFree : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "No `research open` problem has a `sorry`-free proof."
  errorsFound := "`research open` PROBLEMS WITH A `sorry`-FREE PROOF:"
  test declName := do
    let env ← getEnv
    unless categoryOf env declName == some (.research .open) do return none
    let some info := env.find? declName | return none
    if info.value? (allowOpaque := true) |>.any (!·.hasSorry) then
      return m!"has a `sorry`-free proof, so it is not `research open`"
    return none

/-- A statement that refers to its own unknown `<theorem>.answer` asks for a value and must be
tagged `question value`. -/
@[env_linter] def valueQuestionTag : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "Every statement about its own `answer` is tagged `question value`."
  errorsFound := "STATEMENTS ABOUT THEIR OWN `answer` WITHOUT `question value`:"
  test declName := do
    let env ← getEnv
    unless isWritten env declName do return none
    let some info := env.find? declName | return none
    unless info.type.getUsedConstants.contains (declName ++ `answer) do return none
    unless (← getQuestionKind? declName) == some .value do
      return m!"refers to its unknown `{declName ++ `answer}`, so it asks for a value; \
        tag the theorem `@[question value]`"
    return none

/-- A statement refers to no other theorem's unknown `bar.answer`, which is most likely a
copy-and-paste error. A `test` or `API` statement may state a sanity check about one. -/
@[env_linter] def foreignAnswer : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "No statement refers to another theorem's `answer`."
  errorsFound := "STATEMENTS REFERRING TO ANOTHER THEOREM'S `answer`:"
  test declName := do
    let env ← getEnv
    unless isWritten env declName do return none
    if categoryOf env declName matches some .test | some .API then return none
    let some info := env.find? declName | return none
    for c in info.type.getUsedConstants do
      if c.getString! == "answer" && c != declName ++ `answer then
        return m!"refers to `{c}`, the unknown of another question; a statement about its own \
          unknown refers to `{declName ++ `answer}`, and a statement about `{c}` belongs to a \
          `test` or `API` theorem"
    return none

/-! ## Dependence on `sorry` -/

/-- Whether the search follows constant `c`: those of this repository's modules, and those of the
current module, which has no entry in `env.header.moduleNames`. -/
def followsModule (env : Environment) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | none => true
  | some idx => (`FormalConjectures).isPrefixOf env.header.moduleNames[idx]! ||
      (`FormalConjecturesForMathlib).isPrefixOf env.header.moduleNames[idx]!

/-- The constants a declaration depends on: those of its type and value, and for an inductive
type, which has no value, those of the types of its constructors. -/
def dependencies (env : Environment) (info : ConstantInfo) : Array Name := Id.run do
  let mut used := info.type.getUsedConstants ++
    ((info.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
  if let .inductInfo ind := info then
    for ctor in ind.ctors do
      if let some ctorInfo := env.find? ctor then
        used := used ++ ctorInfo.type.getUsedConstants
  return used

/-- The search for one statement, with the results for the constants visited so far. -/
abbrev SearchM := StateT (Std.HashMap Name (Option Name)) Id

/-- The first constant on a path from `root` to `sorryAx`, following definitions, proofs, and
constructors inside this repository, but not the unknown `answer` of a value question. `none` if
`root` does not depend on `sorry` in this way. The constant returned is `sorryAx` itself if
`root` uses it directly. -/
partial def sorrySource (env : Environment) (root : Name) : SearchM (Option Name) := do
  if let some r := (← get)[root]? then return r
  -- Record `root` before searching below it, so that a recursive inductive type or definition
  -- does not send the search around in circles.
  modify (·.insert root none)
  let r ← go root
  modify (·.insert root r)
  return r
where
  go (c : Name) : SearchM (Option Name) := do
    if c == ``sorryAx then return some c
    if c.getString! == "answer" then return none
    unless followsModule env c do return none
    let some info := env.find? c | return none
    for d in dependencies env info do
      if d == ``sorryAx then return some c
      if (← sorrySource env d).isSome then return some c
    return none

/-- A statement does not depend on `sorry` except through an `answer` definition. -/
@[env_linter] def statementSorry : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "No statement depends on `sorry` except through an `answer`."
  errorsFound := "STATEMENTS DEPENDING ON `sorry`:"
  test declName := do
    let env ← getEnv
    unless isWritten env declName do return none
    let some (.thmInfo info) := env.find? declName | return none
    let sources : List (Option Name) :=
      (info.type.getUsedConstants.toList.mapM fun c => sorrySource env c).run' {}
    for src? in sources do
      if let some src := src? then
        if src == ``sorryAx then
          return m!"contains `sorry`; only the `answer` definition of a value question may be \
            left as `sorry`"
        return m!"depends on `sorry` through `{src}`; only the `answer` definition of a value \
          question may be left as `sorry`"
    return none

end FormalConjectures.EnvLinter
