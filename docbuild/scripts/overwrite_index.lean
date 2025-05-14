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
import Scripts.Stats

open Lean
open ProblemAttributes


-- TODO(firsching): instead of re-inventing the wheel here use some html parsing library?
def replaceTag (tag : String) (inputHtmlContent : String) (newContent : String) : IO String :=
    let openTag := s!"<{tag}>"
    let closeTag := s!"</{tag}>"

    -- Find the position right after "<tag>"
    match inputHtmlContent.findSubstr? openTag with
    | none => throw <| IO.userError s!"Opening {openTag} tag not found in inputHtmlContent."
    | some bodyOpenTagSubstring =>
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


run_cmd
  Elab.Command.liftCoreM do
  let file := "./.lake/build/doc/index.html"
  let inputHtmlContent ← IO.FS.readFile file
  let statsString ← getCategoryStatsMarkdown
  let markdownBody :=
      s!"# Welcome to the documentation page for *Formal Conjectures*
## Problem Category Statistics
    {statsString}"
  let  newBody := MD4Lean.renderHtml markdownBody
  let finalHtml ← replaceTag "main" inputHtmlContent newBody.get!
  IO.println finalHtml
