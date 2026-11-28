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

/-! # The Sorry Proof Linter

A definition, instance or structure must not be built from a proof that is still `sorry`, such as
`def δ := (density_exists m α).choose` with `density_exists` proved by `sorry`. Every statement
that mentions such a constant depends on `sorryAx`, so it can never be proved axiom-free, whatever
its proof. The usual fix is to define the constant without the proof: `sInf` or `Classical.epsilon`
of the same predicate, keeping the existence theorem as a separate lemma.

The linter follows the constants used in each new definition (its value) and each new structure or
inductive type (the types of its constructors), through other constants of this repository, and
warns when it reaches a theorem whose proof contains `sorry`. Constants from other packages, such
as Mathlib, are not followed. Intended placeholders (`def foo.answer := sorry`) are not theorems,
so they are not reported.

Inside a `module`, the proofs of theorems imported from other modules are not available, so the
linter only sees `sorry` proofs declared in the same file (or reached through definitions of other
files). This covers the usual pattern, where the existence theorem sits just above the definition.
A constant built from a `sorry` proof in another file, such as an imported instance, is not seen.
-/

public meta section

open Lean Elab Linter Command

register_option linter.style.sorryProof : Bool := {
  defValue := false
  descr := "enable the linter that forbids definitions built from proofs that are still `sorry`"
}

namespace SorryProofLinter

/-- Whether `c` is defined in this file or in a module of this repository. Other packages are not
followed. -/
def isLocal (env : Environment) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | none => true
  | some idx =>
    let mod := (env.header.moduleNames[idx.toNat]!).toString
    mod.startsWith "FormalConjectures"

/-- The constants that `ci` refers to and that the linter follows: the value of a definition or
theorem, and the constructor types of an inductive type. -/
def refs (env : Environment) (ci : ConstantInfo) : Array Name :=
  let ofVal := match ci.value? (allowOpaque := true) with
    | some v => v.getUsedConstants
    | none => #[]
  let ofCtors := match ci with
    | .inductInfo i => i.ctors.toArray.flatMap fun c =>
        (env.find? c).map (·.type.getUsedConstants) |>.getD #[]
    | _ => #[]
  ofVal ++ ofCtors

/-- The theorems whose own proof contains `sorry`, reachable from `start`. -/
def sorryProofs (env : Environment) (start : Array Name) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut stack := start
  let mut out : Array Name := #[]
  while h : stack.size > 0 do
    let c := stack.back
    stack := stack.pop
    if seen.contains c || !isLocal env c then continue
    seen := seen.insert c
    let some ci := env.find? c | continue
    let rs := refs env ci
    if ci matches .thmInfo _ && rs.contains ``sorryAx then
      out := out.push c
    for d in rs do
      unless seen.contains d do stack := stack.push d
  return out

/-- Checks the constant `declName` just added by a command. -/
def checkConst (stx : Syntax) (declName : Name) : CommandElabM Unit := do
  let env ← getEnv
  let some ci := env.find? declName | return
  unless ci matches .defnInfo _ || ci matches .inductInfo _ do return
  let srcs := sorryProofs env (refs env ci)
  unless srcs.isEmpty do
    let names := ", ".intercalate (srcs.toList.map fun n => s!"`{n}`")
    logLintIf linter.style.sorryProof stx m!"`{declName}` is built from the proof of {names}, \
      which is still `sorry`, so every statement that mentions `{declName}` depends on \
      `sorryAx`. Avoid that proof here: for example, define the constant with `sInf` or \
      `Classical.epsilon` of the same predicate."

/-- The name declared by a declaration command, resolved the way `CategoryLinter` does it.
Anonymous instances have no `declId` and are skipped. -/
def declName? (stx : Syntax) : CommandElabM (Option Name) := do
  let decl := stx[1]
  let some declId := decl.find? (·.isOfKind ``Lean.Parser.Command.declId) | return none
  let (shortName, _) := Lean.Elab.expandDeclIdCore declId
  let ns ← getCurrNamespace
  let env ← getEnv
  let name :=
    if (`_root_).isPrefixOf shortName then shortName.replacePrefix `_root_ .anonymous
    else ns ++ shortName
  let isPrivate := (stx[0].find? (·.isOfKind ``Lean.Parser.Command.private)).isSome
  return some (if isPrivate then mkPrivateName env name else name)

/-- The sorry proof linter checks every definition, instance and inductive type declared by a
command. -/
def sorryProofLinter : Linter where
  run := withSetOptionIn fun stx => do
    unless getLinterValue linter.style.sorryProof (← getLinterOptions) do return
    if (← MonadLog.hasErrors) then return
    unless stx.getKind == ``Lean.Parser.Command.declaration do return
    let kind := stx[1].getKind
    unless kind == ``Lean.Parser.Command.definition || kind == ``Lean.Parser.Command.abbrev ||
      kind == ``Lean.Parser.Command.instance || kind == ``Lean.Parser.Command.structure ||
      kind == ``Lean.Parser.Command.inductive do return
    let some n ← declName? stx | return
    checkConst stx n

initialize do
  addLinter sorryProofLinter

end SorryProofLinter
