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

/-! # InfoTree utils

This file contains a few functions that are useful for traversing infotrees.

-/

variable {α σ m} [Monad m]

/-- Visit nodes in an infotree, where state is set only within a single branch. -/
partial def Lean.Elab.InfoTree.visitStateOf [MonadStateOf σ m]
    (visit : ContextInfo → Info → (children : PersistentArray InfoTree) → m Unit) :
    InfoTree → m Unit :=
  go none
where go
  | ctx?, context ctx t => go (ctx.mergeIntoOuter? ctx?) t
  | some ctx, node i cs => do
    let s ← getThe σ
    visit ctx i cs
    discard <| cs.toList.mapM (go <| i.updateContext? ctx)
    set s
  | _, _ => pure ()
