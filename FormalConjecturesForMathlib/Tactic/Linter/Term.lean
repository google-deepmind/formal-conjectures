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

import FormalConjecturesForMathlib.Lean.Elab.InfoTree.Util

open Lean Meta Elab Command

/-- A copy of `ContextInfo.runMetaM` that keeps the messages and passes in the same filename. -/
def Lean.Elab.ContextInfo.runMetaMInCommandElabM {α} (info : ContextInfo) (lctx : LocalContext)
    (x : MetaM α) : Command.CommandElabM α := do
  let x := (withLocalInstances lctx.decls.toList.reduceOption x).run { lctx := lctx } { mctx := info.mctx }
  /-
    We must execute `x` using the `ngen` stored in `info`. Otherwise, we may create `MVarId`s and `FVarId`s that
    have been used in `lctx` and `info.mctx`.
  -/
  let initHeartbeats ← IO.getNumHeartbeats
  let ((a, _), st) ←
    x.toIO {
      options := info.options,
      currNamespace := info.currNamespace,
      openDecls := info.openDecls,
      fileName := (← getFileName),
      fileMap := info.fileMap,
      initHeartbeats
     }
    {
      env := info.env,
      ngen := info.ngen,
      infoState := ← getInfoState,
      traceState := ← getTraceState
    }
  modify fun s =>
    { s with
      messages := s.messages ++ st.messages,
      infoState := st.infoState,
      traceState := st.traceState
    }
  return a

namespace Lean.Elab.Command.Linter

/--
A linter that applies to terms.

The `lint` argument receives both the original syntax and elaborated expression,
provided the option is enabled.
Note that the linter lives in `StateT σ`, so that it can build up state inherited from parent trees.

This doesn't return a `Linter`, as then the caller would have to remember to pass the `name`.
-/
def runTermLinter {σ} [Inhabited σ] (opt : Lean.Option Bool)
    (lint : Term → Expr → StateT σ MetaM Unit) : Command.CommandElab :=
  withSetOptionIn fun cmdStx => do
    let infoTrees := (← get).infoState.trees.toArray
    if (← MonadState.get).messages.hasErrors then return
    let some cmdStxRange := cmdStx.getRange? | return
    for tree in infoTrees do
      (tree.visitStateOf (σ := σ) (m := StateT σ CommandElabM)
        fun ci info _ => do
          -- the warning can be disabled locally
          unless opt.get ci.options do return
          let some range := info.range? | return
          if !cmdStxRange.contains range.start then return
          if let .ofTermInfo ti := info then
            let s ← get
            try
              let (_, s) ← ci.runMetaMInCommandElabM ti.lctx do (lint ⟨ti.stx⟩ ti.expr).run s
              set s
            catch e =>
              logErrorAt ti.stx m!"Thrown from the {opt.name} term linter:{indentD e.toMessageData}"
            ).run' default
    -- Traces from linters are otherwise completely dropped
    -- https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/trace.5Bdebug.5D.20in.20linters/near/485099940
    let traces := (← getTraceState).traces.toArray
    if !traces.isEmpty then
      Lean.logInfo <|.trace { cls := opt.name } .nil (traces.map (·.msg))
