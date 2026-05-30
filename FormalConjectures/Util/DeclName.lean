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

/-!
# Declaration Name Elaborator

Provides the `decl_name%` term elaborator, which resolves an identifier to its fully qualified
`Lean.Name` at compile time. This ensures that references to declarations are checked by the
compiler and will cause build failures if the target declaration is renamed or removed.
-/

open Lean Elab Term in
/-- `decl_name% Foo.bar` resolves the identifier to verify the declaration
exists, then returns the corresponding `Lean.Name`. Build fails if the
declaration is renamed or removed. -/
elab "decl_name% " n:ident : term => do
  let name ← resolveGlobalConstNoOverload n
  return toExpr name
