# Agents and proof evaluations

Use the existing agent for reasoning. The toolkit prepares exact inputs and verifies
submissions. Evaluation adapters are experimental until their recorded acceptance
checks pass. No model is launched by these commands.

## Install guidance

The normal uv installation includes both portable skills. No global agent settings
are changed during installation.

```sh
conjectures skill path
conjectures skill install --dir .agents/skills
conjectures skill install --name formal-conjectures-review --dir .agents/skills
```

`--dir` is the parent discovery directory. For a Claude project use `.claude/skills`;
other hosts can read the path directly or use their usual skill import mechanism.
Reload the agent after installation. Repeating an identical installation succeeds;
different existing guidance is preserved and reported as a conflict.

## Work on one problem

Run `find` and `show`, select an exact declaration, then use `init TARGET --out DIR`.
Initialization now also works outside an FC checkout. It obtains the exact public
source commit and writes `AGENTS.md` into the generated workspace. Public catalog
availability still depends on #5375; `--catalog FILE` explicitly selects a native
extract for qualification.

The agent edits `Submission.lean` and `.lean` files under `Submission/`. `lake build`
provides development feedback. `conjectures verify DIR` reconstructs trusted files
in a fresh workspace and checks only the submitted Lean files. Configuration,
dependency files, compiled artifacts and candidate workflow files are never imported.

Target bindings are retained outside the submission in the operator's user cache.
The generated provenance is descriptive, not permission to change the trusted target.
A copied or moved workspace requires a new `init` at its destination. Local run
inspection works from a generated workspace, without an FC checkout. Use global
executor configuration when operating across multiple workspaces.

## Linux execution without publishing a candidate

The existing GitHub executor remains available. For local files, use a dedicated,
unprivileged Linux worker with systemd, elan, Go, Rust, and no private credentials.
Do not use a general personal workstation as a verifier for adversarial submissions:
Comparator's Landrun policy can read files outside the candidate directory.

```sh
conjectures setup verify --local --global \
  --toolkit /opt/fc --tools /opt/fc-tools --build-tools
conjectures verify ./proof --json
```

`/opt/fc` must be a clean, operator-owned checkout of the trusted toolkit revision.
`--build-tools` explicitly acquires and builds the pinned generator, Comparator,
Landrun, nanoda and toolchain-compatible exporter. Omit it for already-built tools.
Setup records the toolkit revision and binary digests. Each verification rechecks
them and probes systemd's AF_UNIX restriction. No candidate Git commit or push is
required. Results are attributed to the local operator, not GitHub or an independent
hosted authority. Changed binaries require explicit setup again.

## Freeze a suite

A suite names an exact source commit and exact declarations. It does not contain a duplicate
catalog, reference answers or agent credentials. Its **core** is the source plus each case's
`id`, `declaration` and source `path`; images, budgets and exposure notes are not part of it.

```json
{
  "schema_version": "fc.proof-suite.v2",
  "source": {"repository": "OWNER/REPO", "commit": "EXACT_SOURCE_COMMIT"},
  "execution": {
    "solver_image": "registry/fc-eval-solver@sha256:DIGEST",
    "verifier_image": "registry/fc-eval-verifier@sha256:DIGEST",
    "toolkit_commit": "EXACT_VERIFIER_COMMIT",
    "agent_seconds": 1800
  },
  "cases": [{"id": "example", "declaration": "Exact.declaration",
             "path": "FormalConjectures/Example.lean", "exposure": "Describe prior development exposure"}]
}
```

This is a schema example, not an executable release command. Supply full 40-character
commits and 64-character image digests. Floating tags, duplicate cases, unsafe paths and
missing exposure descriptions are rejected.

## Build suite images once

Setup is not part of an attempt. Build two images per suite core, then freeze the suite with
their digests:

1. **Verifier suite image** (`eval-suite.Dockerfile`, target `verifier`), built on the pinned
   verifier base. The trusted controller exports every case once, resolves one shared set of
   pinned Lake packages with the Mathlib cache, builds each Challenge and records a case file
   bound to the core digest. `/tests/test.sh` is part of the image.
2. **Solver suite image** (target `solver`), built on the solver base. It receives only the
   shared packages, read-only, so an agent's first `lake build` needs no network.

`python3 -m conjectures.eval_suite core --suite suite.json` prints the core used as the build
context. Build natively for each architecture; the AF_UNIX filter cannot load under emulation.

```sh
conjectures eval export suite.json --format harbor --out tasks
uvx --from git+https://github.com/harbor-framework/harbor.git@191d1b989bbba1d77c2db23e17aec308d7c08046 harbor run -p ./tasks -a YOUR_AGENT -m YOUR_MODEL
conjectures eval summarize ./jobs --json
```

Export copies each case workspace out of the verifier image, so solver and verifier grade the
same Challenge, and fails if the image carries a different core or toolkit revision. It records
a file-digest manifest and creates one Harbor task per declaration. Each task builds only a thin
solver layer that adds its workspace. Only `/app/Submission.lean` and `/app/Submission/` transfer
to the verifier, which runs from the prebuilt image with `network_mode = "no-network"`. Harbor
owns model access, attempt counts, budgets and trial logs. Agent setup, such as installing an
agent client, is outside `agent_seconds`.

## Verifier image contract

Use Harbor task schema 1.4 with **separate verifier environments**. Base images must be
available by registry digest and support UID/GID 1000. The verifier base needs Python 3.11+,
Git, elan, libseccomp2, the clean pinned toolkit at `/opt/fc`, and already-built tools at
`/opt/fc-tools/{generator,comparator,landrun,nanoda}`, with the compatible exporter built in
`/opt/fc/comparator/verifier`. A suite verifier image adds `/opt/fc-suite` and `/tests/test.sh`.
Keep credentials and agent logs out of both.

At verification the controller checks the task's suite and core digests against the image,
copies the prepared case workspace into container-local storage, links the read-only shared
packages, imports only the submitted Lean files and runs Comparator inside Landrun. Build
outputs never go to the mounted log directory.

The grader adds an inherited AF_UNIX seccomp restriction before running the same
trusted FC controller and Comparator. Existing container restrictions remain in
force; Landrun and both kernels remain required. Missing tools, unsupported emulation,
failed restrictions and mismatched revisions produce infrastructure errors. This is
not a claim that an arbitrary supplied image has passed release qualification.

## Qualified image recipes

`eval-solver.Dockerfile` and `eval-verifier.Dockerfile` ship with the toolkit under
`conjectures/resources`. Build both with an empty context. Every base image, tool
revision and installer is a pinned argument; the verifier's tool pins must equal
`conjectures.proof.PINS`, and it rechecks them at grading time. Push each image to a
registry you control and use the resulting `@sha256` references in the suite.

The recipes build `linux/amd64` images. The solver contains only the Lean toolchain;
harness agents install their own clients. The verifier's AF_UNIX filter blocks
`socket()` only, like the qualified systemd executor. An unnamed `socketpair()`
reaches no existing endpoint, and Git's HTTPS resolver requires one.

[Harbor qualification 35156959562](https://github.com/williamjblair/formal-conjectures/actions/runs/35156959562)
built both recipes at `8c3f82545`, exported a two-case suite and ran four real Harbor
trials with separate verifier environments. See [the receipt](qualification/harbor-e2e-8c3f825.json).
No model was invoked: Harbor's `nop` and `oracle` agents supplied fixed submissions.

| Trial | Retained status | Reward |
| --- | --- | --- |
| Unfinished placeholder | `rejected` (`disallowed_axiom`) | 0 |
| Imports the source theorem | `rejected` (`disallowed_axiom`) | 0 |
| Valid proof | `verified` | 1 |
| Filled answer hole | `assessment_required` | None |

Each verifier took about eight minutes, mostly dependency acquisition. This qualifies
the recipes and grading contract at that revision. It is not an agent benchmark,
and a model-backed run still needs its own retained trial records.

| Retained status | Harbor reward | Meaning |
| --- | --- | --- |
| `verified` | 1 | Exact proof passed the configured formal checks |
| `rejected` | 0 | Submission rejected |
| `assessment_required` | None | Formal checks passed; definition-hole semantics need assessment |
| `error` | None | Execution did not establish an outcome |

An absent reward deliberately prevents infrastructure/manual-assessment cases from
becoming ordinary zero scores. Harbor may display these as verifier errors; use
`fc-result.json` to distinguish them. The summary counts retained verifier attempts,
not missing, timed-out or cancelled trials that never reached grading. Use the harness
trial manifest and frozen suite for the complete denominator. Never silently retry
until a proof passes or drop failed attempts from a reported success rate.

The public corpus and any prior solution exposure must remain visible in evaluation
reports. Successful export is not successful proof, and formal verification is not
source-fidelity review, catalog admission, or maintainer acceptance.
