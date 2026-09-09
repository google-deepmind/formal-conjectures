# Review with conjectures

Use the current agent session, its permissions, and its available tools. No model
login or provider selection belongs to this workflow.

1. Run `conjectures review prepare --pr NUMBER --json`, or
   `conjectures review prepare --changed --json`. Successful preparation exits 0 while retaining
   `awaiting_review`; semantic review is still required. Exit 4 means missing
   coverage or setup, and 1/3 means build failure/execution error. Preserve these
   gaps and record the returned run ID.
2. Read the returned request, procedure, source passages, scoped files under the
   snapshot path, and independent build receipt. Use the recorded head/base. Do
   not replace these inputs with the current checkout or read evaluation keys.
   The existing skill's meaning checks and stopping rules still apply.
3. Fill the returned `draft` path (`review.json`); the template remains available. Record the session's human/agent
   identity and model when known; explicitly say `model unknown` otherwise. The
   identity is self-reported. Never invent usage or claim a blinded session.
   `fresh` means no earlier review records informed this report. For `rereview`,
   retain the prior review/reply files and reference them in `prior_reviews`.
4. When needed, run a witness with
   `conjectures review exec --json --files DIR RUN -- lake env lean scratch/Witness.lean`.
   Put CLI options anywhere before `--`. Each invocation gets a fresh frozen snapshot and witness
   files under `scratch/`; retain its returned evidence path. Run untrusted
   candidate code through this isolation boundary. Scratch success cannot change
   the independent build or establish proof verification.
5. Run `conjectures review finish RUN --json`. For extra documents,
   earlier reviews, or separately produced witness outputs, use `--evidence DIR`
   and reference `evidence/operator/<filename>`. Sources use paths from the request;
   scratch checks use returned paths. Invalid reports leave the run pending for
   correction. Missing sources and checks remain incomplete, even with no findings.
6. Inspect `conjectures run show RUN`. Return the supported findings, coverage gaps,
   and local report location. Publish only when the user has authorized it. Use
   `conjectures evidence publish RUN --dry-run` to inspect the public projection;
   `conjectures evidence publish RUN --post` archives then posts the PR summary.
   If publication fails, retain the completed review and retry publication separately.

For general command help and installation, read the bundled toolkit usage guide or
`conjectures --help`. If the CLI is unavailable, the semantic procedure still works
manually; explicitly record unavailable checks instead of inventing receipts.
