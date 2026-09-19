---
name: conjectures
description: Use the conjectures CLI to browse Formal Conjectures, prepare reviews, develop exact-target Lean proof submissions, or export proof evaluation tasks. Use the current agent session for reasoning and proof work.
---

# Work with Formal Conjectures

Use `conjectures help COMMAND` for the installed interface and `--json` for
structured results. Read `reason`, coverage, paths, and the next action; a successful
command can leave semantic work pending. No model login or second agent is needed.

- Browse with `find QUERY`, then `show TARGET`. Select one exact declaration and
  its recorded revision; variants can have different statements and assumptions.
- For a contribution review, run `review --pr NUMBER` or `review --changed` in FC.
  Read the returned procedure and inputs, write the retained `review.json` draft,
  and run the returned `review finish RUN` command. Preparation is not a review.
- For a proof, run `init DECLARATION --out DIR`. Read the generated `AGENTS.md`.
  Edit only `Submission.lean` and Lean files under `Submission/`. Use Lean feedback
  while working; run `verify DIR` for a fresh check of the exact target. Do not
  change the statement, permitted axioms, dependencies, or verifier configuration.
- For evaluations, export a frozen suite with `eval export SUITE --format harbor --out DIR`.
  The external harness owns attempts, model access, and budgets. Preserve failed,
  interrupted, and errored attempts. Do not inspect reference solutions or keys.

Inspect results with `run show RUN` and `run logs RUN`. An execution error is not
a rejected proof. Definition-hole answers may need semantic assessment even when
formal checks pass. Verification does not establish source fidelity or maintainer
acceptance. Publish or push only when requested; local work stays local by default.
