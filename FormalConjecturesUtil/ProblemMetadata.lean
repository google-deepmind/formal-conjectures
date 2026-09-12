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

public import Lean
public meta import FormalConjecturesUtil.Metadata
public import FormalConjecturesUtil.Attributes.Basic
public import FormalConjecturesUtil.Answer

/-!
# Shared declaration metadata

Extract semantic facts from Lean's environment once for catalog consumers.
The website wire format remains schema 2. Git timestamps are supplied by the
caller and are not used to interpret declarations. Internal and anonymous
examples remain excluded; this module does not assign persistent identities.
-/

@[expose] public meta section

namespace FormalConjectures.Metadata
open Lean ProblemAttributes Google

-- Helper to format Category as string
def categoryToString : Category → String
  | .textbook => "textbook"
  | .research .open => "research open"
  | .research .solved => "research solved"
  | .test => "test"
  | .API => "API"

-- Helper to format FormalProofKind as string
def formalProofKindToString : FormalProofKind → String
  | .formalConjecturesProof => "formal_conjectures"
  | .lean4 => "lean4"
  | .otherSystem => "other_system"

def nameAny (n : Name) (p : String → Bool) : Bool :=
  match n with
  | .anonymous => false
  | .str p' s => p s || nameAny p' p
  | .num p' _ => nameAny p' p

def isInternal (n : Name) : Bool :=
  nameAny n (fun s => s.startsWith "_" || s.startsWith "match_" || s.startsWith "proof_")

/-- Determine the `answerKinds` for a theorem's type expression.

For each `answer(...)` occurrence found in the type,
returns `"Prop"` or `"non-Prop"` depending on the type
of the annotated subexpression. -/
def getAnswerKinds (type : Expr) : MetaM (List String) := do
  let ansExprs := findAnswerExprs type
  ansExprs.toList.mapM fun ansExpr => do
    if ← Meta.isProp ansExpr then
      return "Prop"
    else
      return "non-Prop"

structure ProblemSpec where
  «theorem» : String
  module : String
  category : String
  subjects : List String
  statement : String
  docstring : Option String
  formalProofs : List FormalProofInfo
  hasSorryFreeProof : Bool
  subsets : List String
  answerKinds : List String
  fileFirstAdded : Option String
  fileLastModified : Option String


/-- Serialize `ProblemSpec` to JSON, omitting fields whose keys are in `exclude`. -/
def ProblemSpec.toFilteredJson (info : ProblemSpec) (exclude : Std.HashSet String := {}) : Json :=
  let fields : List (String × Json) :=
    [("theorem", toJson info.theorem),
     ("module", toJson info.module),
     ("category", toJson info.category)]
    ++ (if exclude.contains "subjects" then [] else [("subjects", toJson info.subjects)])
    ++ (if exclude.contains "statement" then [] else [("statement", toJson info.statement)])
    ++ (if exclude.contains "docstring" then [] else [("docstring", toJson info.docstring)])
    ++ (if exclude.contains "formalProofs" || info.formalProofs.isEmpty then [] else
        [("formalProofs", Json.arr (info.formalProofs.map FormalProofInfo.toJson).toArray)])
    ++ (if exclude.contains "hasSorryFreeProof" then [] else
        [("hasSorryFreeProof", toJson info.hasSorryFreeProof)])
    ++ (if info.subsets.isEmpty then [] else [("subsets", toJson info.subsets)])
    ++ (if exclude.contains "answerKinds" then [] else
        [("answerKinds", toJson info.answerKinds)])
    ++ (if exclude.contains "fileFirstAdded" then [] else
        [("fileFirstAdded", toJson info.fileFirstAdded)])
    ++ (if exclude.contains "fileLastModified" then [] else
        [("fileLastModified", toJson info.fileLastModified)])
  Json.mkObj fields

instance : ToJson ProblemSpec where
  toJson info := info.toFilteredJson

/-- Extract the named, categorized theorem declarations from the requested modules.

This observes a declaration's own proof term for `hasSorryFreeProof`; it does
not establish that its transitive assumptions are acceptable. -/
unsafe def extractProblems (moduleNames : Array Name)
    (fileTimestamps : Std.HashMap Name (Option String × Option String) := {}) :
    CoreM (List ProblemSpec) := do
  let env ← getEnv
  let tags ← getTags
  let subjectTags ← getSubjectTags
  let formalProofTags ← getFormalProofTags

  -- Create maps for quick lookup
  let mut categoryMap : Std.HashMap Name (List String) := {}
  let mut categoryFullMap : Std.HashMap Name CategoryTag := {}
  for tag in tags do
    categoryMap := categoryMap.insert tag.declName (categoryToString tag.category :: categoryMap.getD tag.declName [])
    categoryFullMap := categoryFullMap.insert tag.declName tag

  -- Create formal proof map. A declaration may carry several `formal_proof` annotations,
  -- so collect them all rather than keeping whichever arrives last.
  let mut formalProofMap : Std.HashMap Name (List FormalProofTag) := {}
  for tag in formalProofTags do
    formalProofMap :=
      formalProofMap.insert tag.declName (tag :: formalProofMap.getD tag.declName [])

  let mut subjectMap : Std.HashMap Name (List String) := {}
  for tag in subjectTags do
    let subjects := tag.subjects.map (fun (s : AMS) => s!"{s.toNat?.get!}")
    subjectMap := subjectMap.insert tag.declName (subjects ++ subjectMap.getD tag.declName [])

  let mut theoremToSubsets : Std.HashMap Name (List String) := {}

  for (declName, _) in env.constants do
    if let .str (.str grandparent subsetName) "problems" := declName then
      if grandparent.toString == "Subsets" then
        let info ← getConstInfo declName
        if let some val := info.value? then
          try
            let problemsList ← Lean.Meta.MetaM.run' <|
              unsafe Lean.Meta.evalExpr (List Name) (mkApp (mkConst ``List [.zero]) (mkConst ``Name)) val
            for p in problemsList do
              theoremToSubsets := theoremToSubsets.insert p (subsetName :: theoremToSubsets.getD p [])
          catch e =>
            let msg ← e.toMessageData.toString
            IO.eprintln s!"WARNING: Failed to evaluate problems list for {declName}: {msg}"

  let mut allResults : List ProblemSpec := []
  for modName in moduleNames do
    let some modIdx := env.header.moduleNames.findIdx? (· == modName)
      | continue
    let modData := env.header.moduleData[modIdx]!
    for info in modData.constants do
      let name := info.name
      match info with
      | ConstantInfo.thmInfo .. =>
        if !isInternal name then
          let cats := categoryMap.getD name []
          let subjs := subjectMap.getD name []
          if !cats.isEmpty || !subjs.isEmpty then
            if cats.length ≠ 1 then
              throwError m!"Theorem {name} must have exactly one category, found {cats.length}."
            let statement := toString (← Meta.MetaM.run' (Meta.ppExpr info.type))
            let docstring ← findDocString? env name
            if docstring.isNone then
              IO.eprintln s!"WARNING: Theorem {name} (category: {cats.head!}) is missing a docstring"
            -- Extract formal proof info from the separate formal_proof attributes. Each
            -- carries its own `conditions`, since one proof can be conditional while
            -- another of the same statement is not.
            let formalProofs :=
              ((formalProofMap.getD name []).map fun tag =>
                { kind := formalProofKindToString tag.proofKind,
                  link := tag.proofLink,
                  conditions := tag.conditions.map Name.toString : FormalProofInfo })
              |>.toArray.qsort (fun a b => a.sortKey < b.sortKey) |>.toList
            -- Check whether the proof term is sorry-free
            let hasSorryFreeProof :=
              info.value? (allowOpaque := true) |>.any (!·.hasSorry)
            -- Warn about suspicious category / sorry combinations
            if let some catTag := categoryFullMap.get? name then
              match catTag.category, hasSorryFreeProof with
              | .research .open, true =>
                IO.eprintln s!"WARNING: Theorem {name} is categorised as `research open` but has a sorry-free proof"
              | .test, false =>
                IO.eprintln s!"WARNING: Theorem {name} is categorised as `test` but has no sorry-free proof"
              | .API, false =>
                IO.eprintln s!"WARNING: Theorem {name} is categorised as `API` but has no sorry-free proof"
              | _, _ => pure ()
            let subsets := (theoremToSubsets.getD name []).toArray.qsort (· < ·) |>.toList
            -- Determine answerKinds from the elaborated type
            let answerKinds ← Meta.MetaM.run'
              (getAnswerKinds info.type)
            let (fileFirstAdded, fileLastModified) :=
              fileTimestamps.getD modName (none, none)
            allResults := {
              «theorem» := name.toString,
              module := modName.toString,
              category := cats.head!,
              subjects := subjs,
              statement := statement,
              docstring := docstring,
              formalProofs := formalProofs,
              hasSorryFreeProof := hasSorryFreeProof,
              subsets := subsets
              answerKinds := answerKinds
              fileFirstAdded := fileFirstAdded
              fileLastModified := fileLastModified
            } :: allResults
      | _ => pure ()
  return allResults.reverse

end FormalConjectures.Metadata
