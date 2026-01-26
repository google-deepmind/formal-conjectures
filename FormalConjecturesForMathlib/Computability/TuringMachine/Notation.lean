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
import FormalConjecturesForMathlib.Computability.TuringMachine.BusyBeavers

/-! # Turing Machine Parser

This module provides a parser for defining a Turing machine from a simple string description.
The main entry point is the `turing_machine%` elaborator, which takes a string representing the
machine's transitions and constructs a term of type `Machine (Fin m) StateType` where `StateType`
is an inductive type generated on the fly.

## Encoding format

The machine's transitions are encoded as a single string, with each state's transitions
separated by an underscore (`_`).
For each state, a `3m`-character substring defines the behavior:
- The first 3 characters `"ABC"` describe the action when the head reads `0`:
  - `A`: The symbol to write (`0, 1, ..., m-1`).
  - `B`: The direction to move the head (`L` or `R`).
  - `C`: The new state (`A` through `Z`).
- The next 3 characters `"DEF"` describe the action when the head reads `1` using the same format.
- The next 3 characters `"GHI"` describe the action when the head reads `2` using the same format.
- So on...

The character `Z` is reserved for the halting state. The string `"---"` can be used to represent
a transition to the halting state without writing or moving.

Example of a tape: `1RA0LB_0LA---`

There are more examples in `ForMathlib/Test/Computability`.
-/

open Turing BusyBeaver

open Lean Elab Meta Parser Command Term Qq

section Util

private def Alphabet := ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N',
  'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z']

/-- `Char.toDirSyntax c` outputs the syntax corresponding to the character `c` if `c` is
`R` or `L` and throws an error in other cases. This is used when parsing the "direction"
component of turing machine string representations. -/
private def Char.toDirSyntax : Char → TermElabM Term
  | 'R' => `(Dir.right)
  | 'L' => `(Dir.left)
  | char => throwError "Invalid direction {char}."

/-- `Char.toBinarySyntax c` outputs the syntax corresponding to the character `c` if `c` is in
`0, ..., 9` and throws an error in other cases. This is used when parsing the "symbol"
component of turing machine string representations. -/
private def Char.toNumeralSyntax (c : Char) : TermElabM Term := do
  unless c.isDigit do
    throwError m!"Invalid write instruction: {c} is not a numeral."
  -- Compute the value of the digit represented by `c`.
  let n := c.val - '0'.val
  `($(Lean.Quote.quote n.toNat))

/-- `Char.toStateSyntax c stateName` outputs the syntax of the constructor corresponding to `c`
if `c` is a capital letter (i.e. something between `A` and `Z`.). For example, `A` would output
the syntax `stateName.A` where `stateName` is the name of the type used to index sets.
This is used when parsing the "state" component of turing machine string representations. -/
private def Char.toStateSyntax (c : Char) (stateName : Name) (numStates : Nat) : TermElabM Term := do
  unless c.isUpper do
    throwError m!"Invalid state character: {c} should be between A and Z"
  -- The convention is to non-state letters (i.e. any letter above the highest letter denoting a
  -- state) to denote the extra halting state.
  if c.val - 'A'.val ≥ numStates.toUInt32 then
    `(none)
  else
    return Lean.mkIdent <| .str stateName c.toString

/-- `Nat.toStateSyntax n stateName` outputs the syntax of the `n`-th constructor of the type used to
index states. -/
private def Nat.toStateSyntax (n : Nat) (stateName : Name) : TermElabM Term := do
  if n > 25 then
    throwError m!"Invalid state index {n}"
  `($(Lean.mkIdent <| .str stateName Alphabet[n]!.toString))

/-- `String.toStmtSyntax s stateName` parses a component of a Turing machine string representation
and outputs the syntax of the corresponding `(state, statement) : State × Stmt` pair. -/
private def String.toStmtSyntax (s : String) (stateName : Name) (numStates : Nat) : TermElabM Term := do
  let [c_symbol, c_dir, c_state] := s.toList |
    throwError m!"Invalid transition encoding: {s} should be 3 characters long."
  if c_symbol = '-' ∧ c_dir = '-' ∧ c_state = '-' then
    `(none)
  else
    let state ← c_state.toStateSyntax stateName numStates
    let symbol ← c_symbol.toNumeralSyntax
    let direction ← c_dir.toDirSyntax
    let stmt ← `(Stmt.write $symbol $direction)
    `(some ($state, $stmt))

end Util

private def String.nextn (s : String) (p : Pos.Raw) : Nat → Pos.Raw
  | 0 => p
  | n + 1 => Pos.Raw.next s (s.nextn p n)

/--
Take as input a list of strings and return an array of `matchAltExpr` syntaxes
mapping `(state, symbol)` pairs to actions of a Turing Machine,
given by a term of type `Option (State n)`.
-/
def mkMachineMatchAltExpr (L : List String) (stateName : Name) (numSymbols numStates: Nat) :
    TermElabM (Array (TSyntax ``matchAltExpr)) := do
  /-
  The encoding of a TM move by a (sub)string `"ABC"` works as follows:
    - The move the TM is currently at (the dictionary's key) is determined
      by the position of the substring
    - `A` gives the new symbol (`0` or `1`), `B` the direction the head moves
      (`L` or `R`) and `C` the new state (`0, ..., n-1` or `none`)
  -/

  let moves ← L.toArray.zipIdx.mapM fun (s, i) =>
    Array.range numSymbols |>.mapM fun symbolIdx ↦ do
      let pos1 := s.nextn ⟨0⟩ (3 * symbolIdx)
      let pos2 := s.nextn ⟨0⟩ (3 * (symbolIdx + 1))
      let s_first : Term ← (String.Pos.Raw.extract s pos1 pos2).toStmtSyntax stateName numStates
      `(matchAltExpr| | $(← i.toStateSyntax stateName), ($(quote symbolIdx)) => $s_first)

  return moves.flatten

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
  let entryLengths := moveListStr.map String.length |>.dedup
  unless entryLengths.length == 1 do
    throwError "All portions of the string separated by `_` should have the same length."
  unless 3 ∣ entryLengths[0]! do
    throwError "Each chunk of the string should consist of several groups of length 3."
  let numSymbols := entryLengths[0]! / 3
  let stateName := numStates.toStateName
  mkStateType numStates stateName
  let .some stateType ← checkTypeQ (.const stateName []) q(Type)
    | throwError m!"The constant {.ofConstName stateName} is not a type."
  let funConstructors ← mkMachineMatchAltExpr moveListStr (numStates.toStateName) numSymbols numStates
  let tm ← `(term | fun a b => match a, b with $funConstructors:matchAlt*)
  let _ ← synthInstanceQ q(Inhabited $stateType)
  let numSymbolsQ : Q(Nat) := Lean.toExpr numSymbols
  elabTermEnsuringType tm q(Machine (Fin $numSymbolsQ) $stateType)

/-- `turing_machine% tmStringDescription` outputs a term of type `Machine Γ Λ`
where `Γ = Fin 2` and `Λ` is an inductive type constructed on the fly with constructors
`A, B, ...`, and named `State{n}` where `n` is the number of states of the machine.

Warning: if `State{n}` already exists in the environment then this will be reused without checking
that this is the right inductive type - such checks are left to the user.
-/
elab "turing_machine%" str:Lean.Parser.strLit : term =>
  parseTuring str.getString

end Main
