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
import MD4Lean
import Lean
import Batteries.Data.String.Matcher
import FormalConjectures.Util.Attributes
import Mathlib.Data.String.Defs


open Lean
open ProblemAttributes

-- TODO(firsching): make it possible to search for attributes in doc-gen4, likely depends on
-- https://github.com/google-deepmind/formal-conjectures/issues/5
def getCategoryStatsMarkdown : CoreM String := do
  let stats ← getCategoryStats
  let githubSearchBaseUrl := "https://github.com/search?type=code&q=repo%3Agoogle-deepmind%2Fformal-conjectures+"
  return  s!"| Count | Category          |
| ----- | ----------------- |
| {stats (Category.research ProblemStatus.open)} | [Research (open)]({githubSearchBaseUrl}%22category+research+open%22)|
| {stats (Category.research ProblemStatus.solved)} | [Research (solved)]({githubSearchBaseUrl}%22category+research+solved%22)|
| {stats (Category.graduate)} | [Graduate]({githubSearchBaseUrl}%22category+graduate%22)|
| {stats (Category.undergraduate)} | [Undergraduate]({githubSearchBaseUrl}%22category+undergraduate%22)|
| {stats (Category.highSchool)} | [High School]({githubSearchBaseUrl}%22category+high_school%22)|
| {stats (Category.API)} | [API]({githubSearchBaseUrl}%22category+API%22)|
| {stats (Category.test)} | [Tests]({githubSearchBaseUrl}%22category+tests%22)|"

-- TODO(firsching): make it possible to search for subjects in doc-gen4, likely depends on
-- https://github.com/google-deepmind/formal-conjectures/issues/5
def getSubjectStatsMarkdown : CoreM String := do
  let tags ← getSubjectTags

  let mut counts : Std.HashMap AMS Nat := {}
  for tag in tags do
    for subject in tag.subjects do
      counts := counts.insert subject (counts.getD subject 0 + 1)

  let sortedCounts := counts.toArray.qsort (lt := fun (_, c1) (_, c2) => c2 < c1)
  let mut markdownTable := "| Count | AMS # | Subject |\n" ++
                           "| ----- | ----- | ------- |\n "

  for (subject, count) in sortedCounts do
    if count > 0 then
      let desc ← subject.getDesc
      let some num := subject.toNat? | throwError "subject not recognised"
      let numStr := (toString num).leftpad 2 '0';
      markdownTable := markdownTable.append s!"| {count} | {numStr} |{desc} |\n"
  return markdownTable

-- TODO(firsching): instead of re-inventing the wheel here use some html parsing library?
def replaceTag (tag : String) (inputHtmlContent : String) (newContent : String) : IO String := do
  let openTag := s!"<{tag}>"
  let closeTag := s!"</{tag}>"

  -- Find the position right after "<tag>"
  let .some bodyOpenTagSubstring := inputHtmlContent.findSubstr? openTag
    | throw <| IO.userError s!"Opening {openTag} tag not found in inputHtmlContent."
  let contentStartIndex := bodyOpenTagSubstring.stopPos
  -- Find the position of "</tag>"
  let .some bodyCloseTagSubstring := inputHtmlContent.findSubstr? closeTag
    | throw <| IO.userError s!"Closing {closeTag} tag not found in inputHtmlContent."
    -- Ensure the tags are in the correct order
  if contentStartIndex > bodyCloseTagSubstring.startPos then
    throw <| IO.userError s!"{openTag} content appears invalid (start of content is after start of {closeTag} tag)."

  -- Extract the part of the HTML before the original body content (includes "<tag>")
  let htmlPrefix := inputHtmlContent.extract 0 contentStartIndex
  -- Extract the part of the HTML from "</tag>" to the end
  let htmlSuffix := inputHtmlContent.extract bodyCloseTagSubstring.startPos inputHtmlContent.endPos

  -- Construct the new full HTML content
  let finalHtml := htmlPrefix ++ newContent ++ htmlSuffix
  return finalHtml

/--
Runs a `CoreM α` action in an environment where all FormalConjectures modules are imported.
This is useful for accessing declarations and attributes defined in the project.
-/
unsafe def runWithImports {α : Type} (actionToRun : CoreM α) : IO α := do
  -- This assumes a run of `lake exe mk_all; mv FormalConjectures.lean FormalConjectures/All.lean` took place before.
  -- TODO(firsching): avoid this by instead using `Lake.Glob.forEachModuleIn` to generate a list of all modules instead.
  -- Then it would be easily possible to sort out the statements from the Util dir (in tests),
  -- which we probably don't want to count here.
  let moduleImportNames := #[`FormalConjectures.All]
  initSearchPath (← findSysroot)
  let modulesToImport : Array Import := moduleImportNames.map ({ module := · })
  let currentCtx := { fileName := "", fileMap := default }
  Lean.enableInitializersExecution

  Lean.withImportModules modulesToImport {} fun env => do
    let (result, _newState) ← Core.CoreM.toIO actionToRun currentCtx { env := env }
    return result

unsafe def main (args : List String) : IO Unit := do
  let .some file := args.get? 0
    | IO.println "Usage: stats <file>
overwrites the contents of the `main` tag of a html `file` with a welcome page including stats."
  let inputHtmlContent ← IO.FS.readFile file
  let .some graphFile := args.get? 1
    | IO.println "Repository growth graph not supplied, generating docs without graph."
  let graphHtml ← IO.FS.readFile graphFile

  runWithImports do
    let categoryStats ← getCategoryStatsMarkdown
    let subjectStats ← getSubjectStatsMarkdown
    let markdownBody :=
      s!"# Welcome to the *Formal Conjectures* Documentation!

Check out the main
[Formal Conjectures GitHub repository](https://github.com/google-deepmind/formal-conjectures)
for more details.

This page provides an overview of the problem categories and subject classifications used
within the project. For a more detailed explanation of these categories and the AMS subject
classifications, please refer to the
[explanation of features in the project's README](https://github.com/google-deepmind/formal-conjectures?tab=readme-ov-file#some-features).

---

## Problem Category Statistics
{categoryStats}

(note the links above use GitHub search, and so require logging into GitHub)

---

## Subject Category Statistics
{subjectStats}

---

## Repository growth
"
    IO.println markdownBody
    let .some newBody := MD4Lean.renderHtml (parserFlags := MD4Lean.MD_FLAG_TABLES ) markdownBody | throwError "Parsing failed"
    let finalHtml ← replaceTag "main" inputHtmlContent (newBody ++ graphHtml)
    IO.FS.writeFile file finalHtml
