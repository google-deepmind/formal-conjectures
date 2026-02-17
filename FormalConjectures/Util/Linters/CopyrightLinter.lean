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

namespace CopyrightLinter

/-- The part of the expected copyright before the year. -/
def correctCopyrightPrefix : String :=
"/-
Copyright "

/-- The part of the expected copyright after the year. -/
def correctCopyrightSuffix : String :=
" The Formal Conjectures Authors.

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

/-- Check whether a file, given as a `String`, is prefixed with the correct copyright header. -/
def hasCorrectCopyright (file : String) : Bool := Id.run do
  let .some suffix := file.dropPrefix? correctCopyrightPrefix | false
  correctCopyrightSuffix.isPrefixOf (suffix.extract ⟨4⟩ suffix.stopPos).toString

/-- The current correct copyright header. -/
def correctCopyrightHeader : String := correctCopyrightPrefix ++ "2026" ++ correctCopyrightSuffix

/-- info: true -/
#guard_msgs in
#eval hasCorrectCopyright correctCopyrightHeader

register_option linter.style.copyright : Bool := {
  defValue := true
  descr := "enable the copyright header style linter"
}



/-- The copyright linter ensures that every file has the right copyright header. -/
def copyrightLinter : Linter where run := withSetOptionIn fun stx ↦ do
  -- The formal-conjectures CI uses a global import file called `All.lean` but we don't want
  -- to run this linter there.
  if (← getFileName).endsWith "FormalConjectures/All.lean" then return
  let source := (← getFileMap).source
  -- Get the syntax corresponding to the first character in the file since that's where the warning
  -- message will be logged.
  let startingStx : Syntax := .atom (.synthetic ⟨0⟩ ⟨1⟩) <| source.extract ⟨0⟩ ⟨1⟩
  -- We don't want to output an error message when building `FormalConjectures.All`
  unless (← getFileName) == "FormalConjectures.All" || hasCorrectCopyright source do
    Lean.Linter.logLintIf linter.style.copyright startingStx <|
    "The copyright header is incorrect. Please copy and paste the following one:\n"
      ++ correctCopyrightHeader

initialize addLinter copyrightLinter

end CopyrightLinter
