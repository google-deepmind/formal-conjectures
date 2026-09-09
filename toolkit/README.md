# Formal Conjectures toolkit

This dependency PR adds proof workspace commands to the review CLI. Evidence
publication follows in a separate PR. Remote proof qualification remains incomplete.

Use `conjectures` from your existing agent session or directly in a terminal.
The toolkit needs no AI credentials or model configuration. Your agent reads the
FC review skill and conducts the semantic review. The CLI prepares exact inputs,
runs isolated checks, validates reports, and manages proof workspaces and evidence.

Install an exact revision:

```sh
uv tool install git+https://github.com/williamjblair/formal-conjectures.git@COMMIT
conjectures doctor --json
```

Replace `COMMIT` with the full tested revision. Run commands inside your FC checkout.
Configuration lives in `~/.config/conjectures/config.json` or `.conjectures/config.json`:

```json
{"image":"sha256:PINNED_IMAGE_ID","executor":null,"evidence":null,"limits":{"build_seconds":180,"scratch_seconds":60,"scratch_calls":20}}
```

The image uses `scripts/review-report/Dockerfile` and must contain the target's exact
Lean toolchain, Lake configuration, dependency manifest, and trusted cache. Docker
runs candidate code without host credentials or networking. An unavailable image
leaves an explicit build gap; the CLI can still prepare sources for semantic review.
Lean and Lake own dependency pins. Use existing `gh` authentication when needed for
PR access, proof workflow dispatch, or publication. `CONJECTURES_GH` can select an
existing authenticated `gh` wrapper. Old `backend` and `model` fields are ignored
with a migration notice; remove them from toolkit configuration.

## Review in an existing session

Ask your agent to review a PR or local changes using the FC review skill. The same
canonical skill lives in `.agents/skills/formal-conjectures-review/` and is bundled
with the installed toolkit. Codex and OpenCode discover the repository skill.
Claude Code uses the small repository entry point in `.claude/skills/`, which links
to that canonical procedure. Hermes can install the canonical folder with its own
skill manager. You can also ask any agent to read `SKILL.md` explicitly. No global
agent configuration is changed by installing the Python package.

The skill uses these commands:

```sh
conjectures review prepare --pr 4899 --json
conjectures review prepare --changed --base origin/main --json
```

Preparation returns `status: awaiting_review`, reason `awaiting_review`, and exit
code 4. This means the inputs are ready and semantic review is still required.
It returns paths to the frozen request, readable snapshot, sources, procedure,
report template, and independent build receipt. New or modified problem modules
are supported, up to five per run. Broader changes have an explicit unsupported
scope result. Preparation preserves your branch, index, and working files.

Read the returned procedure and fill a copy of `review-template.json`. Describe the
actual session identity; use `model unknown` if unavailable. `context_policy: fresh`
means no prior review records informed the review; it does not assert an isolated
or blinded session. For a rereview, retain the earlier reviews and replies as
supporting evidence. Never read the skill's evaluation keys during semantic review.

When a witness is needed, run a bounded scratch check:

```sh
conjectures review exec --json --files /path/to/witnesses RUN -- lake env lean scratch/Witness.lean
```

Options precede `RUN`. Witness files appear under `/tmp/work/scratch/` in a fresh
container restored from the frozen request. Each command starts fresh; it cannot
change the independent build. Its output gives an evidence path for findings.
Copy additional witnesses into `--files` for subsequent commands. These operation
limits constrain CLI execution, not your agent's overall conversation.

Complete the review:

```sh
conjectures review finish RUN --report /path/to/review.json --json
conjectures run show RUN --json
```

For documentary evidence, prior reviews, or outputs produced using your agent's
own tools, add `--evidence DIR`; reference these as `evidence/operator/<filename>`.
These files are operator evidence. Supplying `checks.json` cannot replace the
controller's build check. Invalid reports leave the run pending so you can fix
and resubmit them. Completed reports are immutable; start a new run for a rereview.

Use `conjectures review prepare --input /path/to/retained-run` to reuse frozen
inputs in a new run with a new independent build. This also accepts downloaded
Actions preparation artifacts. It never reuses a hosted receipt as local proof.

## Inspect and publish

Runs and raw artifacts stay in the gitignored `.conjectures/` directory. Use
`status`, `run list`, `run show`, and `run logs` to inspect them. `run cancel RUN`
cancels a pending local review. A local review has no background model to wait for;
`run wait` returns its current state. Remote proof runs use their configured executor.

```sh
conjectures evidence publish RUN --dry-run
conjectures evidence publish RUN
conjectures evidence publish RUN --post
```

Inspect the public export before publishing. `--post` explicitly archives first,
then posts one advisory PR summary only if the head/base and request order still
apply. `review finish --post` uses this same operation. If publication fails, the
completed review remains available; retry `evidence publish RUN --post`. Publication
requires the configured existing evidence branch and a public committed PR target.
Raw snapshots, complete source documents, invocation logs, and private artifacts
are omitted. A historical review remains evidence about its original inputs.

Exit codes are 0 for a passing result, 1 for a failed check or supported semantic
finding, 2 for invalid input, 3 for an execution error, 4 for incomplete work, and 5
for cancellation. `--json` emits structured reasons; progress goes to stderr.

## Proof workspaces and automation

Use `find QUERY` and `show TARGET` to locate the declaration, `init TARGET --out DIR`
to generate its pinned workspace, and `verify DIR` for configured Linux verification.
A shortcut may have several variants; initialization requires an exact declaration.
The proof workflow and its pins are separate from agent choice or semantic review.
Compilation alone does not verify assumptions. Maintainers decide acceptance.

Default CI performs deterministic checks without model access. The opt-in Actions
pilot only prepares inputs and isolated build evidence. Model adapters remain in
`scripts/review_model_*.py` for explicitly configured hosted use or controlled
evaluations; they are excluded from the installable runtime. The evaluation extra
`.[eval]` supplies MCP only for those experiments. No model calls are made by
`conjectures`, and no seven-minute session limit or uniform token accounting is
claimed for an external agent.
