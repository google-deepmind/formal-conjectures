/-
Copyright 2025 The Formal Conjectures Authors.

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

import Mathlib.Tactic.Linter.Header

open Lean Elab Meta Command Syntax

def correctCopyrightHeader : String :=
"/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the \"License\");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an \"AS IS\" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/"

register_option linter.style.copyright : Bool := {
  defValue := true
  descr := "enable the copyright header style linter"
}

/-- The copyright inter ensures that every file has the right copyright header. -/
def copyrightLinter : Linter where run := withSetOptionIn fun stx ↦ do
  let source := (← getFileMap).source
  -- Get the syntax corresponding to the first character in the file since that's where the warning
  -- message will be logged.
  let startingStx : Syntax := .atom (.synthetic ⟨0⟩ ⟨1⟩) <| source.extract ⟨0⟩ ⟨1⟩
  unless correctCopyrightHeader.data.IsPrefix source.data do
    Lean.Linter.logLint linter.style.copyright startingStx <|
    "The copyright header is incorrect. Please copy and paste the following one:\n"
      ++ correctCopyrightHeader

initialize addLinter copyrightLinter
