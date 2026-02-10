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
