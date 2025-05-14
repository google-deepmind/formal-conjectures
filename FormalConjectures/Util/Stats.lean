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
--TODO(firsching): investigage why this import is needed
import FormalConjectures.Other.BusyBeaverAntihydra
import FormalConjectures.Util.Attributes
import Lean

open Lean ProblemAttributes

-- TODO(firsching): Consider adding links to identify the different categories like
-- https://github.com/search?q=repo%3Agoogle-deepmind%2Fformal-conjectures+%22category+research+open%22&type=code
def getCategoryStatsMarkdown : CoreM String := do
  let stats ← getCategoryStats
  return  s!" | Category        | Count |
  | :-------------- | ----: |
  | Open Problems   | {stats (Category.research ProblemStatus.open)} |
  | Solved Problems | {stats (Category.research ProblemStatus.solved)} |
  | High School     | {stats (Category.highSchool)} |
  | Undergraduate   | {stats (Category.undergraduate)} |
  | Graduate        | {stats (Category.graduate)} |
  | API             | {stats (Category.API)} |
  | Tests           | {stats (Category.test)} |"


unsafe def fetchStatsMarkdown : CoreM String := do
  let moduleImportNames := #[`FormalConjectures]
  let currentCtx ← read

  let modulesToImport : Array Import := moduleImportNames.map ({ module := · })

  let ioProgram : IO String := do
    Lean.enableInitializersExecution

    Lean.withImportModules modulesToImport {} 0 fun enrichedEnv => do
      let coreMActionToRun : CoreM String := getCategoryStatsMarkdown

      let (statsOutputString, _newState) ← Core.CoreM.toIO coreMActionToRun currentCtx { env := enrichedEnv }
      return statsOutputString

  ioProgram

run_cmd
  Elab.Command.liftCoreM do
    let statsOutput : String ← fetchStatsMarkdown
    IO.println statsOutput
