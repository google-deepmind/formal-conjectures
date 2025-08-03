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
import FormalConjectures.ForMathlib.Computability.TuringMachine.Basic

/-! # Turing Machine Parser

This module provides a parser for defining a Turing machine from a simple string description.
The main entry point is the `turing_machine%` elaborator, which takes a string representing the
machine's transitions and constructs a term of type `Machine (Fin 2) StateType` where `StateType`
is an inductive type generated on the fly.

## Encoding format

The machine's transitions are encoded as a single string, with each state's transitions
separated by an underscore (`_`).
For each state, a 6-character substring defines the behavior:
- The first 3 characters `"ABC"` describe the action when the head reads `0`:
  - `A`: The symbol to write (`0` or `1`).
  - `B`: The direction to move the head (`L` or `R`).
  - `C`: The new state (`A` through `Z`).
- The last 3 characters `"DEF"` describe the action when the head reads `1` using the same format.

The character `Z` is reserved for the halting state. The string `"---"` can be used to represent
a transition to the halting state without writing or moving.

-/

open Turing BusyBeaver

open Lean Elab Meta Parser Command Term Qq

section Util

private def Alphabet := ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N',
  'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z']

private def Char.toDirSyntax : Char → TermElabM Term
  | ⟨82, _⟩ => return ← `(Dir.right)
  | ⟨76, _⟩ => return ← `(Dir.left)
  | char => throwError "Invalid direction {char}."

private def Char.toBinarySyntax : Char → TermElabM Term
  | ⟨48, _⟩ => `(0)
  | ⟨49, _⟩ => `(1)
  | char => panic! s!"Invalid write instruction: {char} is not a binary character."

private def Char.toStateSyntax (c : Char) (stateType : Name) : TermElabM Term := do
  if c.val < 65 || c.val > 90 then
    throwError m!"Invalid state character: {c} should be between A and Z"
  -- The convention is to use the character `Z` to denote the extra halting state.
  if c == 'Z' then
    `(none)
  else
    `($(Lean.mkIdent <| .str stateType c.toString))

private def Nat.toStateSyntax (n : Nat) (stateName : Name) : TermElabM Term := do
  if n > 25 then
    throwError m!"Invalid state index {n}"
  `($(Lean.mkIdent <| .str stateName Alphabet[n]!.toString))

private def String.toStmtSyntax (s : String) (stateName : Name) : TermElabM Term := do
  unless s.length == 3 do
    throwError m!"Invalid transition encoding: {s} should be 3 characters long."
  if s == "---" then
    `(none)
  else
    let state ← (s.get! ⟨2⟩).toStateSyntax stateName
    let symbol ← (s.get! ⟨0⟩).toBinarySyntax
    let direction ← (s.get! ⟨1⟩).toDirSyntax
    let stmt ← `(Stmt.write $symbol $direction)
    `(some ($state, $stmt))

end Util

/--
Take as input a list of strings and return an array of `matchAltExpr` syntaxes
mapping `(state, symbol)` pairs to actions of a Turing Machine,
given by a term of type `Option (State n)`.
-/
def mkMachineMatchAltExpr (L : List String) (stateName : Name) :
    TermElabM (Array (TSyntax ``matchAltExpr)) := do
  /-
  The encoding of a TM move by a (sub)string `"ABC"` works as follows:
    - The move the TM is currently at (the dictionary's key) is determined
      by the position of the substring
    - `A` gives the new symbol (`0` or `1`), `B` the direction the head moves
      (`L` or `R`) and `C` the new state (`0, ..., n-1` or `none`)
  -/

  --The moves when the TM head read `0`
  let moves0 ← L.toArray.zipIdx.mapM fun (s, i) => do
    let s_first : Term ← (s.extract ⟨0⟩ ⟨3⟩).toStmtSyntax stateName
    `(matchAltExpr| | $(← i.toStateSyntax stateName), (0 : Fin 2) => $s_first)
  --The moves when the TM head read `1`
  let moves1 ← L.toArray.zipIdx.mapM fun (s, i) => do
    let s_first : Term ← (s.extract ⟨3⟩ ⟨6⟩).toStmtSyntax stateName
    `(matchAltExpr| | $(← i.toStateSyntax stateName), (1 : Fin 2) => $s_first)
  return moves0 ++ moves1

-- The following is extracted as a standalone definition in case we want to later change
-- the naming convention to make clashes harder.
/-- The name of the state type with `n` constructors `A, B, ...`. -/
private def Nat.toStateName (n : Nat) : Name := .mkSimple s!"State{n}"

section Main

/-- `mkStateType n` adds to the environment an inductive type with `n` states
names `State{n}` with constructors the symbols `A, B, ...`, together with the instance
`Inhabited (State{n})`. -/
def mkStateType (n : ℕ) (stateName : Name) : TermElabM Unit := do
  /-
  We may want to have some smarter check done here, e.g. throw an error if the type of the
  constant isn't defeq to the one we want? (note that the instance command we elaborate below already
  implicitely performs a very weak check). -/
  unless ← hasConst stateName do
    let indName : Ident := Lean.mkIdent <| stateName
    -- First construct the inductive type
    let typeConstructors ← (Array.range n).mapM fun i ↦
      `(Command.ctor| | $(Lean.mkIdent <|
        .mkSimple s!"{Alphabet[i]!}"):ident : $(indName))
    let stx ← `(command| inductive $(indName) $typeConstructors:ctor*)
    liftCommandElabM <| elabCommand stx
  -- Create the `inhabited` instance as follows in order to have access to it e.g. in proofs
  let inhabitedStx ← `(command | instance : Inhabited $(Lean.mkIdent stateName) :=
    ⟨$(Lean.mkIdent <| (.str stateName "A"))⟩)
  liftCommandElabM <| elabCommand inhabitedStx

/-- `parseTuring tmStringDescription` outputs the `Expr` corresponding to the Turing
Machine described by the string `tmStringDescription`.

To do so, it
1) Runs `mkStateType` to add the state type to the environment
2) Defines the corresponding Turing Machine as a function using the `match` syntax.

Warning: if a state type (i.e. something with the name `State1, State2, ...`) already
exists in the environment then this will be reused without checking that this is the right
inductive type - such checks are left to the user.
-/
def parseTuring (descr : String) : TermElabM Expr := do
  let moveListStr := descr.splitOn "_"
  let numStates := moveListStr.length
  let stateName := numStates.toStateName
  mkStateType numStates stateName
  let .some stateType ← checkTypeQ (.const stateName []) q(Type)
    | throwError m!"The constant {stateName} is not a type."
  let funConstructors ← mkMachineMatchAltExpr moveListStr (numStates.toStateName)
  let tm ← `(term | fun a b => match a, b with $funConstructors:matchAlt*)
  let _ ← synthInstanceQ q(Inhabited $stateType)
  elabTermEnsuringType tm q(Machine (Fin 2) $stateType)

/-- `turing_machine% tmStringDescription` outputs a term of type `Machine Γ Λ`
where `Γ = Fin 2` and `Λ` is an inductive type constructed on the fly with constructors
`A, B, ...`, and named `State{n}` where `n` is the number of states of the machine.

Warning: if `State{n}` already exists in the environment then this will be reused without checking
that this is the right inductive type - such checks are left to the user.
-/
elab "turing_machine%" str:Lean.Parser.strLit : term =>
  parseTuring str.getString

end Main
