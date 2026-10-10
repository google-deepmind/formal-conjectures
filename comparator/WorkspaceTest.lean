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

open Lean

/-- Run comparator on this workspace's `config.json`, so that `lake test`
is the check. Adapted from `leanprover/lean-eval`'s workspace test template.
The binary comes from `PATH`, or from `COMPARATOR_BIN`. -/
def main : IO UInt32 := do
  let comparatorBin := (← IO.getEnv "COMPARATOR_BIN").getD "comparator"
  try
    let child ← IO.Process.spawn {
      cmd := "lake"
      args := #["env", comparatorBin, "config.json"]
    }
    child.wait
  catch err =>
    IO.eprintln s!"Failed to run comparator via `{comparatorBin}`."
    IO.eprintln "Install comparator, with landrun and lean4export, and put it \
on PATH, or set COMPARATOR_BIN. See leanprover/comparator's README."
    IO.eprintln s!"Original error: {err}"
    pure 1
