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
bundling declaration, module, category, subjects, answer holes and source
range belongs here too, and arrives when `extract_names`' internal
`TheoremInfo` migrates; growing it ahead of its consumers would be schema
fiction.
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

end FormalConjectures.Metadata
end
