/-
Copyright 2025 Google LLC

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

import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Util.Superscript

instance WithLp.instDecidableEq {p} (V : Type*) [DecidableEq V] : DecidableEq (WithLp p V) :=
  ‹DecidableEq V›

/-!
Taken from https://github.com/leanprover-community/mathlib4/pull/17732.

Note that this makes it required to call `Lean.enableInitializersExecution` /
`lean_enable_initializer_execution` in code loading a lean runtime, but we
already do that everywhere internally.
-/
section Notation
open Lean Meta Elab Term Macro TSyntax PrettyPrinter.Delaborator SubExpr

/-- Notation for vectors in Lp space. `!₂[x, y, ...]` is a shorthand for
`(WithLp.equiv 2 _ _).symm ![x, y, ...]`, of type `EuclideanSpace _ (Fin _)`.
This also works for other subscripts. -/
syntax (name := PiLp.vecNotation) "!" noWs subscript(term) noWs "[" term,* "]" : term
macro_rules | `(!$p:subscript[$e:term,*]) => do
  -- override the `Fin n.succ` to a literal
  let n := e.getElems.size
  `((WithLp.equiv $p <| ∀ _ : Fin $(quote n), _).symm ![$e,*])

set_option trace.debug true in
/-- Unexpander for the `!₂[x, y, ...]` notation. -/
@[delab app.DFunLike.coe]
def EuclideanSpace.delabVecNotation : Delab :=
  whenNotPPOption getPPExplicit <| whenPPOption getPPNotation <| withOverApp 6 do
    -- check that the `(WithLp.equiv _ _).symm` is present
    let p : Term ← withAppFn <| withAppArg do
      let_expr Equiv.symm _ _ e := ← getExpr | failure
      let_expr WithLp.equiv _ _ := e | failure
      withNaryArg 2 <| withNaryArg 0 <| delab
    -- to be conservative, only allow subscripts which are numerals
    guard <| p matches `($_:num)
    let `(![$elems,*]) := ← withAppArg delab | failure
    `(!$p[$elems,*])

end Notation
