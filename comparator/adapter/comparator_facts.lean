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
import Lean
import FormalConjecturesUtil.Answer
import FormalConjecturesUtil.Attributes.Basic

/-!
The elaborator-side facts `comparator/adapter/fc_leaneval_importer.py` would otherwise
get by reading Lean with regular expressions.

Given a module and a declaration name, this prints JSON with what the
elaborated environment knows exactly and the text layer can only guess:

- the declaration's source range, for slicing its original text;
- its declaration-header binders, with names and explicitness, for the
  Solution adapter;
- the type of each `sorry` inside the *statement*, which is the type of an
  `answer(sorry)` slot. The `answer_type` field in a `comparator/problems`
  file exists only because surface syntax does not carry this; the
  environment does.

Usage:
  lake exe comparator_facts <Module> <declaration>

The declaration may be given in full or by any whole suffix, the same rule
the Python importer uses.
-/

open Lean Meta

/-- A request matches a name in full, or by dropping any whole prefix. -/
def declares (declared : Name) (requested : String) : Bool :=
  let s := declared.toString
  s == requested || s.endsWith ("." ++ requested)

/-! ## Declaration binder boundaries, from source syntax

A theorem proved by bare `sorry` can be stored as a full-type `sorryAx`, so the
proof value's lambda arity does not reliably separate header parameters from
binders in the conclusion. This subsystem recovers that boundary from the
declaration's source text and matches it against the elaborated telescope;
every binder fact emitted still comes from the environment. -/

/-- Collect every node of one syntax kind. A declaration command must contain
exactly one `declSig`; finding zero or more than one means we did not parse the
source range we thought we did, and the importer fails closed. -/
partial def collectKind (kind : Name) (stx : Syntax) (found : Array Syntax := #[]) :
    Array Syntax :=
  let found := if stx.isOfKind kind then found.push stx else found
  stx.getArgs.foldl (fun acc child => collectKind kind child acc) found

structure SourceBinder where
  name? : Option Name
  info : BinderInfo
  deriving Repr

def sourceBinderName (stx : Syntax) : Except String (Option Name) :=
  if stx.isIdent then .ok (some stx.getId)
  else if stx.isOfKind ``Lean.Parser.Term.hole then .ok none
  else .error s!"unsupported declaration binder name {stx.getKind}: {stx}"

/-- The names and binder kinds introduced by one declaration-header group. -/
def declarationBinderGroup (binder : Syntax) : Except String (Array SourceBinder) := do
  if binder.isIdent || binder.isOfKind ``Lean.Parser.Term.hole then
    return #[{ name? := ← sourceBinderName binder, info := .default }]
  if binder.isOfKind ``Lean.Parser.Term.instBinder then
    let some optionalName := binder[1]?
      | throw s!"malformed instance binder: {binder}"
    let name? ← match optionalName.getArgs[0]? with
      | some name => sourceBinderName name
      | none => pure none
    return #[{ name?, info := .instImplicit }]
  let info? :=
    if binder.isOfKind ``Lean.Parser.Term.explicitBinder then some BinderInfo.default
    else if binder.isOfKind ``Lean.Parser.Term.implicitBinder then some .implicit
    else if binder.isOfKind ``Lean.Parser.Term.strictImplicitBinder then some .strictImplicit
    else none
  let some info := info?
    | throw s!"unsupported declaration binder syntax {binder.getKind}: {binder}"
  let some names := binder[1]?
    | throw s!"malformed declaration binder: {binder}"
  if names.getArgs.isEmpty then
    throw s!"declaration binder has no names: {binder}"
  names.getArgs.mapM fun name => do
    return { name? := ← sourceBinderName name, info }

def declarationSignature (command : Syntax) : Except String Syntax := do
  let signatures := collectKind ``Lean.Parser.Command.declSig command
  let [signature] := signatures.toList
    | throw s!"expected exactly one declaration signature, found {signatures.size}"
  return signature

def declarationBinders (command : Syntax) : Except String (Array SourceBinder) := do
  let signature ← declarationSignature command
  let some header := signature[0]?
    | throw "declaration signature has no binder header"
  header.getArgs.foldlM (fun binders binder => do
    return binders ++ (← declarationBinderGroup binder)) #[]

/-- Number of parameters written before the colon in a declaration header.

This is deliberately a syntax boundary, not a proof-value heuristic:
`theorem foo (n : Nat) : P n` has one declaration parameter, while
`theorem foo : ∀ n : Nat, P n` has none. Lean 4.32 may store a theorem proved
by `sorry` as a `sorryAx` at the full forall type, with no lambda wrappers, so
the old proof-value lambda arity silently reported zero for the first form.
The syntax supplies only the boundary; names, types, and explicitness still
come from the elaborated telescope below. -/
def declarationBinderCount (command : Syntax) : Except String Nat := do
  return (← declarationBinders command).size

def sourceBinderMatches (source : SourceBinder) (elaborated : LocalDecl) : Bool :=
  source.info == elaborated.binderInfo && match source.name? with
    | some name => name == elaborated.userName
    | none => true

def sourceBindersMatchAt (source : Array SourceBinder) (elaborated : Array LocalDecl)
    (start : Nat) : Bool :=
  source.zipIdx.all fun (binder, offset) =>
    match elaborated[start + offset]? with
    | some candidate => sourceBinderMatches binder candidate
    | none => false

/-- Locate the end of the declaration parameters in the elaborated telescope.

Lean inserts used outer `variable`s before the binders written in the
declaration header. We therefore locate the exact typed/named header sequence
inside the telescope and retain everything through its end. This handles
Köthe's `{R} [Ring R]` outer parameters as well as ordinary self-contained
headers. Multiple matches are rejected rather than guessed. -/
def declarationParameterBoundary (command : Syntax) (conclusion : Array SourceBinder)
    (elaborated : Array LocalDecl) : Except String Nat := do
  let source ← declarationBinders command
  if source.isEmpty then
    if conclusion.size > elaborated.size then
      throw s!"source conclusion has {conclusion.size} binders, but the elaborated type has only {elaborated.size}"
    let boundary := elaborated.size - conclusion.size
    unless sourceBindersMatchAt conclusion elaborated boundary do
      throw s!"source conclusion binders {repr conclusion} do not match the elaborated telescope suffix"
    return boundary
  if source.size > elaborated.size then
    throw s!"source header has {source.size} binders, but the elaborated type has only {elaborated.size}"
  let starts := (Array.range (elaborated.size - source.size + 1)).filter
    (sourceBindersMatchAt source elaborated)
  let [start] := starts.toList
    | throw s!"expected one match for {source.size} source-header binders in the elaborated telescope, found {starts.size}"
  return start + source.size

def parseDeclarationBinderCount (env : Environment) (source : String) : Except String Nat := do
  let command ← Parser.runParserCategory env `command source
  declarationBinderCount command

inductive ScanToken where
  | signatureColon
  | bodyMarker
  | comma
  | arrow
  | iff
  | openParen
  | openBrace
  | openBracket
  | openStrict
  | closeParen
  | closeBrace
  | closeBracket
  | closeStrict

def scanTokenAt (wanted : ScanToken) (chars : Array Char) (i : Nat) : Option Nat :=
  match wanted with
  | .signatureColon =>
    if chars[i]? == some ':' && chars[i + 1]? != some '=' then some 1 else none
  | .bodyMarker =>
    if chars[i]? == some ':' && chars[i + 1]? == some '=' then some 2 else none
  | .comma => if chars[i]? == some ',' then some 1 else none
  | .arrow =>
    if chars[i]? == some '→' then some 1
    else if chars[i]? == some '-' && chars[i + 1]? == some '>' then some 2
    else none
  | .iff => if chars[i]? == some '↔' then some 1 else none
  | .openParen => if chars[i]? == some '(' then some 1 else none
  | .openBrace => if chars[i]? == some '{' then some 1 else none
  | .openBracket => if chars[i]? == some '[' then some 1 else none
  | .openStrict => if chars[i]? == some '⦃' then some 1 else none
  | .closeParen => if chars[i]? == some ')' then some 1 else none
  | .closeBrace => if chars[i]? == some '}' then some 1 else none
  | .closeBracket => if chars[i]? == some ']' then some 1 else none
  | .closeStrict => if chars[i]? == some '⦄' then some 1 else none

/-- Find syntax punctuation at delimiter depth zero, ignoring comments and
strings. This scanner does not interpret terms; it only lets us replace the
result type with `True` before asking Lean's real command parser to read the
declaration header. Scoped notation in the result therefore cannot make an
otherwise ordinary header unparseable. -/
partial def findTopLevelToken (wanted : ScanToken) (text : String) : Option (Nat × Nat) :=
  let chars := text.toList.toArray
  let rec loop (i paren brace bracket strict blockComment : Nat)
      (lineComment inString escaped : Bool) : Option (Nat × Nat) :=
    if i >= chars.size then none else
    let current := chars[i]!
    let next := chars[i + 1]?
    if lineComment then
      loop (i + 1) paren brace bracket strict blockComment (current != '\n') inString false
    else if blockComment > 0 then
      if current == '/' && next == some '-' then
        loop (i + 2) paren brace bracket strict (blockComment + 1) false inString false
      else if current == '-' && next == some '/' then
        loop (i + 2) paren brace bracket strict (blockComment - 1) false inString false
      else
        loop (i + 1) paren brace bracket strict blockComment false inString false
    else if inString then
      if escaped then loop (i + 1) paren brace bracket strict 0 false true false
      else if current == '\\' then loop (i + 1) paren brace bracket strict 0 false true true
      else loop (i + 1) paren brace bracket strict 0 false (current != '"') false
    else if current == '-' && next == some '-' then
      loop (i + 2) paren brace bracket strict 0 true false false
    else if current == '/' && next == some '-' then
      loop (i + 2) paren brace bracket strict 1 false false false
    else if current == '"' then
      loop (i + 1) paren brace bracket strict 0 false true false
    else if paren == 0 && brace == 0 && bracket == 0 && strict == 0 then
      match scanTokenAt wanted chars i with
      | some width => some (i, width)
      | none => match current with
        | '(' => loop (i + 1) 1 brace bracket strict 0 false false false
        | '{' => loop (i + 1) paren 1 bracket strict 0 false false false
        | '[' => loop (i + 1) paren brace 1 strict 0 false false false
        | '⦃' => loop (i + 1) paren brace bracket 1 0 false false false
        | _ => loop (i + 1) paren brace bracket strict 0 false false false
    else match current with
      | '(' => loop (i + 1) (paren + 1) brace bracket strict 0 false false false
      | ')' => loop (i + 1) (paren - 1) brace bracket strict 0 false false false
      | '{' => loop (i + 1) paren (brace + 1) bracket strict 0 false false false
      | '}' => loop (i + 1) paren (brace - 1) bracket strict 0 false false false
      | '[' => loop (i + 1) paren brace (bracket + 1) strict 0 false false false
      | ']' => loop (i + 1) paren brace (bracket - 1) strict 0 false false false
      | '⦃' => loop (i + 1) paren brace bracket (strict + 1) 0 false false false
      | '⦄' => loop (i + 1) paren brace bracket (strict - 1) 0 false false false
      | _ => loop (i + 1) paren brace bracket strict 0 false false false
  loop 0 0 0 0 0 0 false false false

def sliceChars (text : String) (start stop : Nat) : String :=
  String.ofList (text.toList.toArray.extract start stop).toList

def forallBinders (term : Syntax) : Except String (Array SourceBinder) := do
  let some marker := term[0]?
    | throw s!"malformed forall syntax: {term}"
  unless marker.isAtom && (marker.getAtomVal == "∀" || marker.getAtomVal == "forall") do
    throw s!"expected forall syntax, got {term.getKind}: {term}"
  let some binderSlot := term[1]?
    | throw s!"forall syntax has no binder: {term}"
  let mut binders := #[]
  if binderSlot.isOfKind `null then
    for binder in binderSlot.getArgs do
      binders := binders ++ (← declarationBinderGroup binder)
  else if binderSlot.isIdent then
    binders := binders.push { name? := some binderSlot.getId, info := .default }
  else
    let some name := binderSlot.getArgs[0]?
      | throw s!"unsupported forall binder syntax {binderSlot.getKind}: {binderSlot}"
    binders := binders.push { name? := ← sourceBinderName name, info := .default }
  let some predicate := term[2]?
    | throw s!"forall syntax has no predicate slot: {term}"
  let isBareTypeSpec := predicate.getArgs[0]?.any
    (·.isOfKind ``Lean.Parser.Term.typeSpec)
  if !predicate.isNone && !isBareTypeSpec then
    binders := binders.push { name? := none, info := .default }
  return binders

/-- Parse only the leading Pi structure of a result type. The remainder is
replaced with `True` before parsing, so scoped term notation later in the
statement is irrelevant. -/
partial def conclusionBinders (env : Environment) (text : String) : Except String (Array SourceBinder) := do
  let text := text.trimAsciiStart.toString
  let chars := text.toList.toArray
  if chars[0]? == some '(' then
    let afterOpen := sliceChars text 1 text.length
    match findTopLevelToken .closeParen afterOpen with
    | some (close, width) =>
      let trailing := sliceChars afterOpen (close + width) afterOpen.length
      if trailing.trimAscii.isEmpty then
        return ← conclusionBinders env (sliceChars afterOpen 0 close)
    | none => pure ()
  let unicodeForall := chars[0]? == some '∀' && chars[1]?.any fun c =>
    c.isWhitespace || c == '(' || c == '{' || c == '[' || c == '⦃'
  let asciiForall := text.startsWith "forall" && chars[6]?.any fun c =>
    c.isWhitespace || c == '(' || c == '{' || c == '[' || c == '⦃'
  if unicodeForall || asciiForall then
    let some (comma, width) := findTopLevelToken .comma text
      | throw "leading forall has no top-level comma"
    let forallPrefix := sliceChars text 0 (comma + width)
    let command ← Parser.runParserCategory env `command
      ("theorem _boundary : " ++ forallPrefix ++ " True := by trivial")
    let signature ← declarationSignature command
    let some typeSpec := signature[1]?
      | throw "synthetic forall signature has no result type"
    let some term := typeSpec[1]?
      | throw "synthetic forall result type is malformed"
    let here ← forallBinders term
    let rest := sliceChars text (comma + width) text.length
    return here ++ (← conclusionBinders env rest)
  let unicodeExists := chars[0]? == some '∃' && chars[1]?.any fun c =>
    c.isWhitespace || c == '(' || c == '{' || c == '[' || c == '⦃'
  let asciiExists := text.startsWith "exists" && chars[6]?.any fun c =>
    c.isWhitespace || c == '(' || c == '{' || c == '[' || c == '⦃'
  if unicodeExists || asciiExists then
    return #[]
  match findTopLevelToken .arrow text, findTopLevelToken .iff text with
  | some (arrow, width), none =>
    let rest := sliceChars text (arrow + width) text.length
    return #[{ name? := none, info := .default }] ++ (← conclusionBinders env rest)
  | _, _ => return #[]

structure DeclarationText where
  beforeNameEnd : String
  afterNameEnd : String

def firstHeaderGroup (text : String) : Option (Nat × ScanToken × ScanToken × Char × Char) :=
  let candidates := #[
    (.openParen, .closeParen, '(', ')'),
    (.openBrace, .closeBrace, '{', '}'),
    (.openBracket, .closeBracket, '[', ']'),
    (.openStrict, .closeStrict, '⦃', '⦄')]
  candidates.foldl (init := none) fun best (openToken, closeToken, opener, closer) =>
    match findTopLevelToken openToken text with
    | none => best
    | some (position, _) => match best with
      | none => some (position, openToken, closeToken, opener, closer)
      | some current =>
        if position < current.1 then some (position, openToken, closeToken, opener, closer)
        else best

/-- Erase binder *types* while preserving binder names and kinds. The
elaborated telescope supplies the types; this parser pass needs only the
surface boundary. Erasing types prevents scoped notation inside a binder type
from making the header impossible to parse out of its original file context. -/
partial def sanitizeHeaderBinders (text : String) : Except String String := do
  let some (start, _, closeToken, opener, closer) := firstHeaderGroup text
    | return text
  let before := sliceChars text 0 start
  let afterOpen := sliceChars text (start + 1) text.length
  let some (close, width) := findTopLevelToken closeToken afterOpen
    | throw s!"unclosed declaration binder beginning with {opener}"
  let inner := sliceChars afterOpen 0 close
  let rest := sliceChars afterOpen (close + width) afterOpen.length
  let universeGroup := opener == '{' && before.trimAsciiEnd.toString.endsWith "."
  let rewritten := if universeGroup then
      String.singleton opener ++ inner ++ String.singleton closer
    else match findTopLevelToken .signatureColon inner with
      | some (colon, _) =>
        String.singleton opener ++ sliceChars inner 0 colon ++ " : True" ++
          String.singleton closer
      | none =>
        if opener == '[' then "[True]"
        else String.singleton opener ++ inner ++ String.singleton closer
  return before ++ rewritten ++ (← sanitizeHeaderBinders rest)

/-- Turn an exact declaration slice into a parser-safe header command and the
original result type. -/
def DeclarationText.headerAndResult (text : DeclarationText) : Except String (String × String) := do
  let some (colon, width) := findTopLevelToken .signatureColon text.afterNameEnd
    | throw "declaration header has no top-level result colon"
  let rawHeader := sliceChars text.afterNameEnd 0 colon
  let header := text.beforeNameEnd ++ (← sanitizeHeaderBinders rawHeader) ++
    " : True := by trivial"
  let afterColon := sliceChars text.afterNameEnd (colon + width) text.afterNameEnd.length
  let result := match findTopLevelToken .bodyMarker afterColon with
    | some (body, _) => sliceChars afterColon 0 body
    | none => afterColon
  return (header, result)

/-- Read the exact declaration range from the source module. The elaborated
environment remains authoritative for the range and telescope; parsing the
slice is only how we recover where the source header ended. -/
def declarationSource (modName : Name) (ranges : DeclarationRanges) : IO (Except String DeclarationText) := do
  let some path ← (← getSrcSearchPath).findModuleWithExt "lean" modName
    | return .error s!"source file for {modName} was not found"
  let source ← IO.FS.readFile path
  let fileMap := FileMap.ofString source
  let start := fileMap.ofPosition ranges.range.pos
  let stop := fileMap.ofPosition ranges.range.endPos
  let nameStop := fileMap.ofPosition ranges.selectionRange.endPos
  if start > nameStop || nameStop > stop || stop > source.rawEndPos then
    return .error s!"invalid declaration range for {modName}: {repr ranges.range}"
  return .ok {
    beforeNameEnd := source.toRawSubstring.extract start nameStop |>.toString
    afterNameEnd := source.toRawSubstring.extract nameStop stop |>.toString }

def binderBoundarySelfTest (env : Environment) : IO UInt32 := do
  let cases : Array (String × Nat) := #[
    ("theorem t (n : Nat) (hn : 1 < n) : True := by trivial", 2),
    ("theorem t : ∀ n : Nat, 1 < n → True := by intro; trivial", 0),
    ("theorem t (x y : Nat) {α : Type} {{β : Type}} [i : Inhabited α] z : True := by trivial", 6)
  ]
  for (source, expected) in cases do
    match parseDeclarationBinderCount env source with
    | .ok actual =>
      if actual != expected then
        IO.eprintln s!"binder-boundary self-test expected {expected}, got {actual}: {source}"
        return 1
    | .error message =>
      IO.eprintln s!"binder-boundary self-test failed: {message}: {source}"
      return 1
  let mkLocal (index : Nat) (name : Name) (info : BinderInfo) : LocalDecl :=
    .cdecl index { name := `_selfTest |>.appendIndexAfter index } name (.sort .zero) info .default
  let outerAndHeader := #[
    mkLocal 0 `R .implicit,
    mkLocal 1 `instR .instImplicit,
    mkLocal 2 `I .implicit,
    mkLocal 3 `hI .default,
    mkLocal 4 `n .default,
    mkLocal 5 `instN .instImplicit]
  let alignmentCases : Array (String × String × Array LocalDecl × Nat) := #[
    ("theorem t {I : Type} (hI : True) (n : Type*) [Fintype n] : True := by trivial",
      "True", outerAndHeader, 6),
    ("theorem t (n : Nat) (hn : 1 < n) : True := by trivial",
      "True", #[mkLocal 0 `n .default, mkLocal 1 `hn .default], 2),
    ("theorem t : ∀ n : Nat, True := by intro; trivial",
      "∀ n : Nat, True", #[mkLocal 0 `R .default, mkLocal 1 `n .default], 1),
    ("theorem t : ∀ n : Nat, 1 < n → True := by intro; trivial",
      "∀ n : Nat, 1 < n → True", #[mkLocal 0 `n .default, mkLocal 1 `h .default], 0),
    ("theorem t : True ↔ ∃ n : Nat, 1 < n → True := by simp",
      "True ↔ ∃ n : Nat, 1 < n → True", #[], 0),
    ("theorem t : ∃ f : Nat → Nat, ∀ n, True → f n = f n := by simp",
      "∃ f : Nat → Nat, ∀ n, True → f n = f n", #[], 0),
    ("theorem t : True → (∀ n : Nat, 1 < n → True) := by simp",
      "True → (∀ n : Nat, 1 < n → True)",
      #[mkLocal 0 `h₁ .default, mkLocal 1 `n .default, mkLocal 2 `h₂ .default], 0)
  ]
  for (source, resultType, elaborated, expected) in alignmentCases do
    let result := do
      let command ← Parser.runParserCategory env `command source
      let conclusion ← conclusionBinders env resultType
      declarationParameterBoundary command conclusion elaborated
    match result with
    | .ok actual =>
      if actual != expected then
        IO.eprintln s!"parameter-alignment self-test expected {expected}, got {actual}: {source}"
        return 1
    | .error message =>
      IO.eprintln s!"parameter-alignment self-test failed: {message}: {source}"
      return 1
  IO.println "binder-boundary self-test passed"
  return 0

/-! ## Environment extraction -/

def binderJson (name : Name) (bi : BinderInfo) : Json :=
  Json.mkObj [("name", toJson name.toString), ("explicit", toJson bi.isExplicit)]

def moduleOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some idx => (env.header.moduleNames[idx.toNat]?.getD Name.anonymous).toString
  | none => ""

/-- Declared by this repository, as opposed to arriving with `import Mathlib`. -/
def isFCLocal (env : Environment) (n : Name) : Bool :=
  (moduleOf env n).startsWith "FormalConjectures"

/-- The FC-local constants a declaration needs, dependencies before dependents.

Post-order over the dependency graph, expanding through both the type and the
value of each FC-local constant: a definition's body names constants its type
does not, and `ChallengeDeps` has to carry them or the copy will not elaborate.
Mathlib and core constants are not expanded, since they arrive with
`import Mathlib`. -/
partial def fcOrder (env : Environment) (n : Name)
    (seen : Std.HashSet Name) (acc : Array Name) : Std.HashSet Name × Array Name :=
  if seen.contains n then (seen, acc) else
    let seen := seen.insert n
    match env.find? n with
    | none => (seen, acc)
    | some info =>
      let fromValue := match info.value? with
        | some v => v.getUsedConstants
        | none => #[]
      -- An inductive has no value, and its fields live in the constructor
      -- rather than in its own type: `structure EdgeN (N D : Nat) where u : V N`
      -- has type `Nat → Nat → Type`, which never mentions `V`. Without the
      -- constructors here the closure still contains `V`, reached some other
      -- way, but orders it after `EdgeN`, and the copy does not elaborate.
      let fromCtors := match info with
        | .inductInfo val => val.ctors.toArray
        | _ => #[]
      let children := (info.type.getUsedConstants ++ fromValue ++ fromCtors).filter
        fun c => isFCLocal env c && c != n
      let (seen, acc) := children.foldl (fun p c => fcOrder env c p.1 p.2) (seen, acc)
      (seen, acc.push n)

unsafe def runWithImports {α : Type} (moduleNames : Array Name)
    (actionToRun : MetaM α) : IO α := do
  initSearchPath (← getBuildDir)
  let imports := moduleNames.map fun n => { module := n }
  Lean.enableInitializersExecution
  let env ← Lean.importModules imports {} (trustLevel := 1024) (loadExts := true)
  -- Twice the default budget, in the context's raw units, which are a
  -- thousand times the `maxHeartbeats` option's: 800000 here meant "800" and
  -- killed the first query. Finite, so a pathological statement errors and is
  -- caught rather than grinding forever, which maxHeartbeats := 0 did.
  let ctx := { fileName := "", fileMap := default, maxHeartbeats := 400000000 }
  let (result, _) ← Core.CoreM.toIO (actionToRun.run' {} {}) ctx { env := env }
  return result

/-- Resolve within one module. Names declared elsewhere are not candidates,
which is what lets one environment holding every module still disambiguate
`conjecture_1_1` the way a per-module import does. -/
def resolveIn (env : Environment) (modName : Name) (declName : String) :
    Except String Name :=
  let inModule (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some idx => env.header.moduleNames[idx.toNat]? == some modName
    | none => false
  -- No `isInternal` filter: `erdos_340.variants._33_mem_sub` has a component
  -- starting with an underscore, which that heuristic calls internal. The
  -- whole-suffix rule in `declares` already keeps auxiliary declarations out,
  -- since `foo.proof_1` is not a suffix match for `foo`.
  let matches_ := env.constants.toList.filterMap fun (n, _) =>
    if declares n declName && inModule n then some n else none
  match matches_ with
  | [] => .error s!"{declName} not found in {modName}"
  | [n] => .ok n
  | _ =>
    match matches_.filter (·.toString == declName) with
    | [n] => .ok n
    | _ => .error s!"{declName} is ambiguous: {matches_}"

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | ["--self-test"] =>
    runWithImports #[`Mathlib] do binderBoundarySelfTest (← getEnv)
  | [modName, declName] =>
    runWithImports #[modName.toName] do
      let env ← getEnv
      match resolveIn env modName.toName declName with
      | .error msg => IO.eprintln msg; return 1
      | .ok n => emit env modName.toName n declName
  | _ =>
    IO.eprintln "usage: comparator_facts <Module> <declaration> | --self-test"
    return 1
where
  emit (env : Environment) (modName name : Name) (decl : String) : MetaM UInt32 := do
    let some info := env.find? name | IO.eprintln "vanished"; return 1
    let some ranges ← findDeclarationRanges? name
      | IO.eprintln s!"{name} has no source range"; return 1
    -- The statement's sorries are `answer(sorry)` slots; a proof's sorry is
    -- not in the *type*, so everything found here is a slot.
    -- `findAnswerExprs` is the repository's own detection: it reads the
    -- annotation the `answer` elaborator leaves, rather than guessing from
    -- `sorryAx` applications.
    let answerTypes ← forallTelescope info.type fun _ body => do
      let found := Google.findAnswerExprs body
      found.mapM fun a => do pure (toString (← ppExpr (← inferType a)))
    let sourceResult ← declarationSource modName ranges
    let declarationText ← match sourceResult with
      | .ok source => pure source
      | .error message => throwError message
    let (header, resultType) ← match declarationText.headerAndResult with
      | .ok pieces => pure pieces
      | .error message => throwError message
    let command ← match Parser.runParserCategory env `command header with
      | .ok command => pure command
      | .error message =>
        throwError "could not recover declaration parameters for {name}: {message}"
    let conclusion ← match conclusionBinders env resultType with
      | .ok binders => pure binders
      | .error message =>
        throwError "could not recover conclusion parameters for {name}: {message}"
    let binders ← forallTelescope info.type fun xs _ => do
      let declarations ← xs.mapM fun x => x.fvarId!.getDecl
      let arity ← match declarationParameterBoundary command conclusion declarations with
        | .ok arity => pure arity
        | .error message =>
          throwError "could not align declaration parameters for {name}: {message}"
      (declarations.extract 0 arity).mapM fun d =>
        pure (binderJson d.userName d.binderInfo)
    let rangeJson := rangeToJson (some ranges)
    -- Only the statement's dependencies: the proof is replaced by `sorry` in
    -- the generated Challenge, so nothing the value names has to be carried.
    let direct := info.type.getUsedConstants.filter (isFCLocal env)
    let (_, ordered) := direct.foldl (fun p c => fcOrder env c p.1 p.2)
      (({} : Std.HashSet Name), (#[] : Array Name))
    -- The equation compiler and `decide` leave constants like
    -- `Finset.greedySidon.aux._proof_1` and `.match_1` in the closure. They
    -- have no source range because they have no source: copying the parent
    -- declaration's text regenerates them. Emit them separately so the
    -- importer can check each one has an ancestor that is being copied,
    -- rather than dropping them silently.
    let mut deps := #[]
    let mut generated := #[]
    for d in ordered.filter (· != name) do
      match ← findDeclarationRanges? d with
      | some r =>
        deps := deps.push <| Json.mkObj [
          ("name", toJson d.toString),
          ("module", toJson (moduleOf env d)),
          ("range", rangeToJson (some r))]
      | none => generated := generated.push (toJson d.toString)
    -- The `@[category ...]` tag, spelled the way the attribute is written.
    -- lean-eval displays open conjectures apart from its evaluation set, so
    -- the importer needs to know which of the two a declaration is; the tag
    -- lives in the environment extension, not in anything the text layer
    -- could read reliably.
    let category := match (ProblemAttributes.categoryExt.getState env).toList.find?
        (·.declName == name) with
      | some tag => Json.str <| match tag.category with
        | .research .open => "research open"
        | .research .solved => "research solved"
        | .textbook => "textbook"
        | .test => "test"
        | .API => "API"
      | none => Json.null
    let payload := Json.mkObj [
      ("declaration", toJson decl),
      ("name", toJson name.toString),
      ("category", category),
      ("range", rangeJson),
      ("binders", toJson binders.toList),
      ("answerTypes", toJson answerTypes.toList),
      ("dependencies", toJson deps.toList),
      ("generatedDependencies", toJson generated.toList)]
    IO.println payload.pretty
    return 0
  rangeToJson (ranges : Option DeclarationRanges) : Json :=
    match ranges with
    | some r => Json.mkObj [
        ("startLine", toJson r.range.pos.line),
        ("startColumn", toJson r.range.pos.column),
        ("endLine", toJson r.range.endPos.line),
        ("endColumn", toJson r.range.endPos.column)]
    | none => Json.null
