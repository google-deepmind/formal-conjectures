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
import MD4Lean
import Lean
import Batteries.Data.String.Matcher
import FormalConjectures.Util.Attributes


open Lean
open ProblemAttributes

-- TODO(firsching): Consider adding links to identify the different categories like
-- https://github.com/search?q=repo%3Agoogle-deepmind%2Fformal-conjectures+%22category+research+open%22&type=code
-- or even better make it possible to search for attributes in doc-gen4
def getCategoryStatsMarkdown : CoreM String := do
  let stats ← getCategoryStats
  return  s!"| Category        | Count |
| --------------- | ----- |
| Open Problems   | {stats (Category.research ProblemStatus.open)} |
| Solved Problems | {stats (Category.research ProblemStatus.solved)} |
| High School     | {stats (Category.highSchool)} |
| Undergraduate   | {stats (Category.undergraduate)} |
| Graduate        | {stats (Category.graduate)} |
| API             | {stats (Category.API)} |
| Tests           | {stats (Category.test)} |"



-- TODO(firsching): instead of re-inventing the wheel here use some html parsing library?
def replaceTag (tag : String) (inputHtmlContent : String) (newContent : String) : IO String :=
    let openTag := s!"<{tag}>"
    let closeTag := s!"</{tag}>"

    -- Find the position right after "<tag>"
    let .some bodyOpenTagSubstring := inputHtmlContent.findSubstr? openTag
      | throw <| IO.userError s!"Opening {openTag} tag not found in inputHtmlContent."
      let contentStartIndex := bodyOpenTagSubstring.stopPos

      -- Find the position of "</tag>"
      match inputHtmlContent.findSubstr? closeTag with
      | none => throw <| IO.userError s!"Closing {closeTag} tag not found in inputHtmlContent."
      | some bodyCloseTagSubstring=>
        -- Ensure the tags are in the correct order
        if contentStartIndex > bodyCloseTagSubstring.startPos then
          throw <| IO.userError s!"{openTag} content appears invalid (start of content is after start of {closeTag} tag)."
        else
          -- Extract the part of the HTML before the original body content (includes "<tag>")
          let htmlPrefix := inputHtmlContent.extract 0 contentStartIndex

          -- Extract the part of the HTML from "</tag>" to the end
          let htmlSuffix := inputHtmlContent.extract bodyCloseTagSubstring.startPos inputHtmlContent.endPos

          -- Construct the new full HTML content
          let finalHtml := htmlPrefix ++ newContent ++ htmlSuffix
          return finalHtml


unsafe def fetchStatsMarkdown : IO String := do
  -- This assumes a run of `lake exe mk_all; mv FormalConjectures.lean FormalConjectures/All.lean` took place before.
  -- TODO(firsching): avoid this by instead using `Lake.Glob.forEachModuleIn` to generate a list of all modules instead.
  let moduleImportNames := #[`FormalConjectures.All]
  searchPathRef.set compile_time_search_path%
  let modulesToImport : Array Import := moduleImportNames.map ({ module := · })
  let currentCtx := { fileName := "", fileMap := default }
  Lean.enableInitializersExecution

  Lean.withImportModules modulesToImport {} 0 fun env => do
    let coreMActionToRun : CoreM String := getCategoryStatsMarkdown

    let (statsOutputString, _newState) ← Core.CoreM.toIO coreMActionToRun currentCtx { env := env }
    return statsOutputString


unsafe def main (args : List String) : IO Unit := do

  match args.get? 0 with
  | some file =>
    let inputHtmlContent ← IO.FS.readFile file

    let statsString ← fetchStatsMarkdown
    let markdownBody :=
       s!"# Welcome to the documentation page for *Formal Conjectures*
## Problem Category Statistics
{statsString}"
    let .some newBody := MD4Lean.renderHtml (parserFlags := MD4Lean.MD_FLAG_TABLES ) markdownBody | throw <| .userError "Parsing failed"
    let finalHtml ← replaceTag "main" inputHtmlContent newBody
    IO.FS.writeFile file finalHtml
  | _         => IO.println "Usage: stats <file>
overwrites the contents of the `main` tag of a html `file` with a weclome page including stats."
