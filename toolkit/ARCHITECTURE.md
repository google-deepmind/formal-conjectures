# Agent sessions and the FC toolkit

Decision recorded 9 September 2026. This supersedes the OAuth-first contributor
journey in the implementation plan. The contributor runtime now implements this
boundary. Qualification and upstream adoption remain separate.

## Contributor experience

Use the agent already running in the contributor's workspace. Ask it to review a
PR or local changes using the FC review skill. That session owns model selection,
provider authentication, permissions, conversation, and any agent orchestration.
FC does not read, copy, or mount its model credentials, create a second agent
session, or require an AI-provider configuration.

Provide one portable Agent Skills bundle containing the existing review procedure
and short toolkit instructions. Keep one canonical source and use each host's
normal skill discovery or installation mechanism. Codex and OpenCode can discover
`.agents/skills`; Claude Code uses a short entry point under `.claude/skills`; Hermes can
install the bundle using its skill manager. Do not add provider-specific review
implementations, a plugin framework, or an MCP server for this workflow.

The CLI remains usable by a human writing a review. Installing it must not require
an agent SDK or credentials for an AI provider.

## Responsibilities

| Component | Responsibility |
| --- | --- |
| Existing agent session | Read the procedure and prepared inputs, investigate meaning, produce findings and questions, report its available identity and context. |
| `conjectures` | Resolve exact inputs, retain snapshots and sources, run isolated checks, validate and assemble reports, manage proof workspaces and evidence. |
| Qualified Linux executor | Reconstruct trusted proof inputs, run the pinned verifier, return typed results and receipts. |
| FC website and workflow board | Display published records, exact applicability, coverage, history, and outstanding work. |

A local operator can edit local files. Local evidence remains attributed to that
operator; report validation does not make it independently hosted verification.
The agent never supplies a replacement independent build or verifier verdict.

## Review interface

Use preparation and completion under `review`, with optional isolated scratch
execution through `review exec`. Interface:

```sh
conjectures review prepare --pr 4941 --json
conjectures review prepare --changed --json
conjectures review finish RUN --json
conjectures run show RUN
conjectures evidence publish RUN
```

Preparation freezes the PR head/base or local snapshot, collects directly cited
sources, runs the independent scoped build, and returns paths to the request,
source passages, snapshot, report template, build receipt, and instructions.
It records `awaiting_review`; preparation is never presented as a completed
semantic review. Unavailable checks and sources remain explicit coverage gaps.

The existing agent reads those files, applies the skill, and writes the existing
review contract. Finish validates its request binding and evidence references,
assembles the report with controller-produced checks, and retains its outcome.
Invalid output leaves the run awaiting correction. Scratch evidence is separately
attributed and cannot replace the independent build receipt. Publishing remains
explicit and rechecks freshness after archiving. Use the existing evidence
publisher for an explicitly requested advisory PR comment.

The contributor usually issues one natural-language instruction in their agent;
the skill carries out these steps. The CLI help explains both phases for people
using a terminal directly. Do not add an interactive agent shell to `conjectures`.

`doctor`, `find`, `show`, `check`, `init`, `verify`, `status`, run inspection, and
proof execution retain their roles. `doctor` checks FC tools, pins, executor and
publication access as applicable. Existing `gh` authentication remains relevant
for GitHub operations. It does not check model-provider logins.

## Evidence and automation

Preserve exact requests, source references, build receipts, semantic reports,
verification results, and publication provenance. Record agent/model identity,
usage, and session references only when the host exposes them; mark unavailable
values explicitly. Self-reported metadata is not independently observed usage.
Do not invent costs or require transcript access. Respect the session's existing
permissions and context; do not describe an ongoing conversation as a fresh,
blinded evaluation.

The CLI enforces limits on operations it owns: source retrieval, subprocesses,
builds, and verification. The skill supplies stopping guidance for semantic work.
A portable skill cannot enforce a uniform seven-minute or 20-tool-call limit on
an arbitrary host session. Controlled model evaluations may impose such limits
in their separate evaluation harness.

For an explicitly enabled headless GitHub review, the workflow may invoke its
chosen existing agent runtime, then use the same preparation and completion
operations. Keep any retained API adapter confined to that optional hosted or
evaluation path. Default CI can run deterministic checks with no model access.
Do not build a general provider-dispatch layer before a concrete hosted need.

## Convergence requirements

- N2: split preparation/build from report completion; remove the default Codex
  launcher, model/backend flags, AI authentication checks, and production MCP
  dependency. Keep the established review request/report contracts.
- Keep controlled model adapters and grading keys outside the installed runtime.
  Historical invocation failures and reports remain readable.
- #5356: consume the shared deterministic operations. Keep model generation
  disabled until a specific hosted runtime and its credentials are configured.
- Pilot: use existing agent sessions on the frozen cases. Preserve the five
  failed prototype invocations as infrastructure failures. Record any new attempt
  separately, including its context; do not silently replace the earlier trial.
  Human adjudication remains required before making review-accuracy claims.
- Update #4394 and #5376 to describe this contributor journey and remove the
  mandatory OAuth pilot. Keep the proof and handoff acceptance journeys.
- Qualify report validation, stale inputs, source gaps, poisoned-build isolation,
  and operation with no AI credentials. Smoke-test portable skill discovery in
  supported hosts; do not make provider-specific review accuracy a compatibility
  claim.

## Primary references checked

- [Codex skills](https://learn.chatgpt.com/docs/build-skills)
- [Claude Code skills](https://code.claude.com/docs/en/skills)
- [OpenCode skills](https://opencode.ai/docs/skills/)
- [Hermes skills](https://hermes-agent.nousresearch.com/docs/user-guide/features/skills/)
- [Agent Skills standard](https://agentskills.io/home)

The 0.2 CLI provides human output by default and separates command status from the
retained mathematical outcome. See README.md for exit codes and setup. Proof and
publication remain experimental until the release acceptance journeys pass.
