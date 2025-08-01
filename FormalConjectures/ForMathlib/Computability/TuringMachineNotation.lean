import FormalConjectures.ForMathlib.Computability.TuringMachine

open Turing BusyBeaver

section

open Lean Elab Meta Parser Command Term Qq


def Char.toDir (c : Char) : Dir := if c.val == 82 then Dir.right else Dir.left

--Outputs the alphabet index if `c` is a capital letter, e.g. `A -> 0`, `Z -> 25`
def Char.toAlphabetNat (c : Char) : Nat :=
  let AN := (c.val.toNat - 65 : Nat)
  if AN < 15 then AN else panic! "Bad state encodding"

def Alphabet := ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P',
  'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z']

/--
Take as input a list of strings and return an array of `matchAltExpr` syntaxes
mapping `(state, symbol)` pairs to actions of a Turing Machine,
given by a term of type `Option (State n)`.
-/
def getStateDict (L : List String) (stateType : Name) : TermElabM (Array (TSyntax ``matchAltExpr)) := do
  /-
  The encoding of a TM move by a (sub)string `"ABC"` works as follows:
    - The move the TM is currently at (the dictionary's key) is determined
      by the position of the substring
    - `A` gives the new symbol (`0` or `1`), `B` the direction the head moves (`L` or `R`) and `C` the new state (`0, ..., n-1` or `none`)
  -/
  let dirToStx : Dir → TermElabM Term
    | .left => do return ← `(Dir.left)
    | .right => do return ← `(Dir.right)

  let natToStateStx (n : Nat) : TermElabM Term := do
    let .some stateChar := Alphabet.get? n
      | throwError "All state characters should be between A and Z"
    return ← `($(Lean.mkIdent <| .str stateType stateChar.toString))

  let toOptionState (s : String) : TermElabM Term := do
    if s.length != 3 then return ← `(none) else
      if '-' ∈ s.toList then return ← `(none) else
        let state ← natToStateStx (s.get! ⟨2⟩).toAlphabetNat
        let stmt ← `(Stmt.write $(quote (s.get! ⟨0⟩).toString.toNat!) $(← dirToStx (s.get! ⟨1⟩).toDir))
        return ← `(some ($state, $stmt))
  --The moves when the TM head read `0`
  let moves0 ← L.toArray.zipIdx.mapM fun (s, i) => do
    let s_first : Term ← toOptionState (s.extract ⟨0⟩ ⟨2⟩)
    return ← `(matchAltExpr| | $(← natToStateStx i), (0 : Fin 2) => $s_first)
  --The moves when the TM head read `1`
  let moves1 ← L.toArray.zipIdx.mapM fun (s, i) => do
    let s_first : Term ← toOptionState (s.extract ⟨3⟩ ⟨6⟩)
    return ← `(matchAltExpr| | $(← natToStateStx i), (1 : Fin 2) => $s_first)
  return moves0 ++ moves1

def mkStateType (n : ℕ) : TermElabM Unit := do
  let stateName := .mkSimple s!"State{n}"
  if ← hasConst stateName then do return
  let indName : Ident := Lean.mkIdent <| stateName
  -- First construct the inductive type
  let typeConstructors : List (TSyntax ``ctor) ←
    (List.range n).mapM fun i ↦ `(Command.ctor| | $(Lean.mkIdent <|
      .mkSimple s!"{Alphabet[i]!}"):ident : $(indName))
  let typeConstructors := typeConstructors.toArray
  let stx ← `(command| inductive $(indName) $typeConstructors:ctor*)
  Lean.liftCommandElabM <| elabCommand stx
  -- Create the inhabited instance as follows in order to have access to it e.g. in proofs
  let inhabitedStx ←
     `(command | instance : Inhabited $(Lean.mkIdent (.mkSimple s!"State{n}"))
      := ⟨$(Lean.mkIdent <| (.mkStr2 s!"State{n}" "A"))⟩)
  Lean.liftCommandElabM <| elabCommand inhabitedStx

def parseTuring (descr : String) : TermElabM Expr := do
  let moveListStr := descr.splitOn "_"
  let nStates := moveListStr.length
  mkStateType nStates
  match ← checkTypeQ (.const (.mkSimple s!"State{nStates}") []) q(Type) with
  | some stateType =>
    let funConstructors ← getStateDict moveListStr (.mkSimple s!"State{nStates}")
    let tm ← `(term | fun a b => match a, b with $funConstructors:matchAlt*)
    -- let defaultEltName := Name.mkStr2 s!"State{nStates}" "A"
    -- let defaultElt : Q($stateType) := .const defaultEltName []
    -- let _ : Q(Inhabited $stateType) := q(⟨$defaultElt⟩)
    let _ ← synthInstanceQ q(Inhabited $stateType)
    let type := q(Machine (Fin 2) $stateType)
    try
      let expr ← elabTermEnsuringTypeQ tm type
      return (expr : Expr)
    catch _ =>
      IO.println "ohno"
    return default
  | none => throwError "Invalid state type"

end

elab "turing_machine%" str:Lean.Parser.strLit : term => do
  Lean.Elab.Term.withDeclName `FindABetterName do
    parseTuring str.getString

#check (turing_machine% "1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA")
