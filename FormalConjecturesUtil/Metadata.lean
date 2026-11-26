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

/-!
# Canonical problem metadata

The website, the Erdős status checker, the proof-link checker, the comparator
workspace generator and the review tooling all need overlapping facts about
this repository's declarations, and each has been re-deriving them. This
module is where the shared representation lives, so that one semantic fact is
interpreted once.

It starts deliberately small: `FormalProofInfo` is the schema
`extract_names` exports as `formalProofs` (`schemaVersion` 2), moved here so
its next consumer imports it rather than restating it. A `ProblemSpec`
bundling declaration, module, category, subjects, question kind and source
range belongs here too, and arrives when `extract_names`' internal
`TheoremInfo` migrates; growing it ahead of its consumers would be schema
fiction.

`openSteps` and `restsOn` are here for the same reason: what a proof rests on is read off the
environment once, by one function, instead of each tool deciding it again.
-/

public section
open Lean

namespace FormalConjectures.Metadata

/-- One formal proof attached to a declaration. Assumptions belong to the
individual proof, not to the conjecture: a statement can carry a conditional
proof and an unconditional one at once, and Erdős 427 does. -/
public structure FormalProofInfo where
  kind : String
  link : String
  conditions : List String

public def FormalProofInfo.toJson (proof : FormalProofInfo) : Json :=
  Json.mkObj
    [("kind", Lean.toJson proof.kind),
     ("link", Lean.toJson proof.link),
     ("conditions", Lean.toJson proof.conditions)]

/-- A key that orders the proofs of one declaration deterministically.

The attribute state is a `HashSet`, so it does not preserve the order the
annotations were written in. Conditions are part of the key: two proofs may
share kind and link and differ only in what they assume. -/
public def FormalProofInfo.sortKey (proof : FormalProofInfo) : String :=
  proof.kind ++ " " ++ proof.link ++ " " ++ String.intercalate "," proof.conditions

/-- Drop the compiler's auxiliary components (`_proof_1`, `match_1`, private
prefixes), so a reached declaration is reported by the name a reader wrote. -/
def userFacingName (n : Name) : Name := Id.run do
  let mut n := privateToUserName n
  while n.isInternal && !n.isAnonymous do
    n := n.getPrefix
  return n

/-- The open statements `declName` rests on: every declaration its statement or
proof reaches, through any number of steps, whose own statement or proof is
`sorry`. `declName` itself is not listed.

A problem is stated once, with `sorry`. Anything that uses it, a variant, a
reduction, a test, rests on it, and this names it, so the open step is read
off the environment rather than restated or re-solved elsewhere. Empty exactly
when `#print axioms declName` shows no `sorryAx` beyond `declName`'s own.

The walk only enters declarations whose axioms include `sorryAx`. Those are a
lookup for imported declarations, so the rest of Mathlib is never traversed. -/
partial def openSteps (declName : Name) : CoreM (Array Name) := do
  let env := (← getEnv).setExporting false
  let rec visit (c : Name) (s : NameSet × NameSet) : CoreM (NameSet × NameSet) := do
    let (seen, found) := s
    if seen.contains c || c == ``sorryAx then return s
    let seen := seen.insert c
    unless (← collectAxioms c).contains ``sorryAx do return (seen, found)
    let some info := env.find? c | return (seen, found)
    let value? := info.value? (allowOpaque := true)
    let found :=
      if c != declName && (info.type.hasSorry || value?.any (·.hasSorry)) then
        found.insert (userFacingName c)
      else found
    let mut s := (seen, found)
    for d in info.type.getUsedConstants ++ (value?.map (·.getUsedConstants)).getD #[] do
      s ← visit d s
    if let .inductInfo v := info then
      for d in v.ctors do s ← visit d s
    return s
  let (_, found) ← visit declName ({}, {})
  return (found.erase (userFacingName declName)).toArray.qsort Name.lt

/-- The axioms every Mathlib proof may rest on. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Everything `declName` rests on beyond `standardAxioms`: the open statements of
`openSteps`, by name; `native` when native evaluation (`native_decide`,
`decide +native`) was used, whose per-proof auxiliary axioms Lean names
`…._native.….ax_<n>`; and any other axiom, by name. `sorryAx` itself is not
listed: the open statements say where it comes from.

Empty means only the standard axioms: the statement is settled. -/
def restsOn (declName : Name) : CoreM (Array String) := do
  let axioms := (← collectAxioms declName).filter
    fun a => a != ``sorryAx && !standardAxioms.contains a
  let isNative (a : Name) := a.components.contains `_native
  let native := if axioms.any isNative then #["native"] else #[]
  let others := (axioms.filter (!isNative ·)).map Name.toString
  return (← openSteps declName).map Name.toString ++ native ++ others

end FormalConjectures.Metadata
end
