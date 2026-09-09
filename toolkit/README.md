# Formal Conjectures toolkit

This focused branch implements review, catalog, and checks. Proof and evidence
commands arrive in their dependent PRs; release-wheel examples install the combined
fork release candidate. Unavailable operations report `unavailable_command`.

`conjectures` browses FC problems, prepares contribution reviews for your existing
agent, and retains reports and proof evidence. It needs no AI login or model
configuration. Your agent conducts semantic review; the CLI handles deterministic
operations. Version 0.2.0rc2 is a **fork release candidate**. Proof verification and
public evidence are experimental pending the full acceptance journeys.

## Try or install

Install [uv](https://docs.astral.sh/uv/getting-started/installation/) first. On macOS
with Homebrew, run `brew install uv`. The official macOS/Linux installer is:

```sh
curl -LsSf https://astral.sh/uv/install.sh | sh
```

Restart your shell after installation. `--python 3.11` selects the tested Python
version; uv can download it when it is unavailable locally.
Try without permanently installing the toolkit:

```sh
uvx --python 3.11 --from https://github.com/williamjblair/formal-conjectures/releases/download/toolkit-v0.2.0rc2/formal_conjectures_toolkit-0.2.0rc2-py3-none-any.whl conjectures doctor
```

Install for regular use:

```sh
uv tool install --python 3.11 https://github.com/williamjblair/formal-conjectures/releases/download/toolkit-v0.2.0rc2/formal_conjectures_toolkit-0.2.0rc2-py3-none-any.whl
conjectures find erdos/730
conjectures show erdos/730
```

These browsing commands and `doctor` work without a checkout, Lean, Docker, or
GitHub login. An unavailable statement or evidence feed is shown explicitly.
Supported systems are macOS and Linux, including WSL. Native Windows is not supported.

To reproduce the qualified RC1 Git revision directly:

```sh
uv tool install --python 3.11 "git+https://github.com/williamjblair/formal-conjectures.git@9c8f6c25de7d73d8f285ece597ee6a727cd81fdd"
```

For local development, run `uv tool install --editable .` inside this repository.
If `conjectures` is not found, run `uv tool update-shell` and restart your shell.
To upgrade a URL-pinned installation, use `uv tool install --force` with the next
release's wheel URL. To uninstall, run `uv tool uninstall formal-conjectures-toolkit`.
PyPI publication is deferred until maintainer acceptance; do not assume the package
is available there. Release artifacts and SHA256SUMS identify each build.

## Catalog and provenance

Default browsing requires the full native catalog published by FC #5375. Until
that PR merges and its full site build deploys, `find` and `show` report
`catalog_not_published` with exit code 4. They do not use the older website
projection, a fork mirror, or a local checkout as an implicit substitute.

After deployment, the CLI verifies the catalog against its published descriptor
and caches it in the user cache for 24 hours. The same cache works inside and
outside a checkout. `--refresh` checks immediately; `--offline` makes no network
requests. If an automatic refresh fails, a retained valid snapshot is labelled
stale. Old statement-free caches are ignored.

```sh
conjectures show Erdos/92 --refresh
conjectures find 'arithmetic progression' --offline
conjectures show Erdos/92 --json
```

`show` prints Lean-derived statements, sources, conditions, variants, the catalog
revision, and commit-pinned source links. Published data does not include local
uncommitted edits. `--catalog FILE` explicitly selects a native extract for local
qualification. Missing provenance stays unknown; missing statement text returns
exit code 4. `init` defaults to the published catalog's exact repository/commit.
An unversioned local catalog requires explicit `--repository` and `--source-ref`.

Evidence applicability uses the catalog repository and revision, not the current
checkout's branch. Results for changed revisions remain historical; variants do
not inherit each other's proof results. Recorded evidence and maintainer acceptance
are separate.

## Review a contribution

Run inside your FC checkout, or pass `--repo /path/to/formal-conjectures`.
Ask your existing agent:

> Use the formal-conjectures-review skill and CLI to review PR 4941. Keep the report local.

The CLI never starts a second agent. The canonical skill lives in
`.agents/skills/formal-conjectures-review/` and is bundled with the package. A small
Claude Code entry point links to it. Other agents can read that SKILL.md directly;
installation does not change their global configuration.

Prepare your build environment once:

```sh
conjectures doctor --for review
conjectures setup review
```

Setup requires running Docker and GitHub access through your existing `gh` login.
It builds an isolated Linux image from an upstream-main revision and the bundled
trusted recipe, then saves its digest. Downloads/builds can take several minutes.
It does not build the environment from PR code or need an evaluation cache.
`setup review --image sha256:...` selects an existing qualified local image instead.
Each review checks exact toolchain, Lake configuration, and dependency-manifest
compatibility. If upstream pins change, run setup again. Host credentials and network
access are absent during candidate execution.

```sh
conjectures review --pr 4941
# Equivalent: conjectures review prepare --pr 4941
conjectures review --changed --base origin/main
```

Semantic review supports one to five new or modified problem modules. Infrastructure,
shared utilities, deleted files, and broader changes need ordinary review. In
particular, the toolkit integration branch itself is not a suitable `--changed` demo.
Preparation preserves your branch, index, and files. It returns an exact run ID,
source coverage, build result, procedure, readable snapshot, and writable `review.json`.

Read the returned procedure and inputs, then have your agent fill that run's draft.
Record actual human/agent identity; say `model unknown` when it is unavailable.
The review remains `awaiting_review` until completion:

```sh
conjectures review finish RUN
conjectures run show RUN
```

Replace RUN with the returned ID. `--report FILE` selects another review JSON;
`--evidence DIR` retains extra documents under `evidence/operator/`. Invalid reports
remain correctable. Completed reports are immutable; prepare a new run for a rereview.
`review prepare --input DIR` replays retained inputs with a new independent build.

For a bounded witness, use:

```sh
conjectures review exec RUN --files ./witnesses -- lake env lean scratch/Witness.lean
```

Options can appear before or after RUN, before `--`. Witness command arguments after
`--` are passed unchanged. Each invocation starts from a fresh frozen snapshot.
Scratch success cannot replace the independent build receipt.

## Inspect work

```sh
conjectures status
conjectures run list --limit 10 --status awaiting_review
conjectures run show latest
conjectures run logs latest
conjectures run logs RUN --artifact controller/build.json
conjectures check --changed
```

Read-only commands accept `latest` or a unique ID prefix. Mutating commands require
an explicit ID or unique prefix. `run logs` displays retained output. `check` reports
an empty changed scope as a successful no-op and explains unsupported shared changes.
It does not equate building with proof verification.

## Proof workspaces (experimental)

```sh
conjectures show erdos/730
conjectures init EXACT_DECLARATION --out ../proof
conjectures setup verify --repository OWNER/REPO --ref FULL_COMMIT
conjectures verify ../proof
conjectures run wait RUN --timeout 600
conjectures run cancel RUN
```

Select the exact declaration from `show`. Initialization uses an isolated checkout
of its retrievable source commit and leaves your checkout unchanged. Develop the
proof externally, then explicitly commit and push the public workspace before verify.
The configured executor must already exist, have a tag pointing to its exact commit,
and match the bundled workflow policy;
setup does not create tags, deploy, or dispatch it. GitHub dispatch uses the tag;
the returned run must still match the configured commit exactly. Policy matching is not proof qualification.
The current workflow is restricted to the qualification fork. There is no automatic
publication of local/private work or fallback to an unqualified executor.

Waiting polls until a result or timeout. Ctrl-C stops waiting and leaves remote work
running; use `run cancel` explicitly. Cancellation requested and confirmed are distinct.
Verification records distinguish rejection from execution errors using typed results.

## Inspect and publish evidence (experimental)

```sh
conjectures setup evidence --repository OWNER/REPO --branch DATA_BRANCH
conjectures evidence publish RUN --dry-run
conjectures evidence publish RUN
conjectures evidence publish RUN --post
```

Setup selects an existing public data branch; it creates no branch and publishes
nothing. Dry-run creates a local public export and lists its files, omissions, and
destination. Inspect the files before publishing. Raw snapshots, complete source
documents, invocation logs, and private artifacts stay local. Reports remain attributed
to their producer; they do not confer maintainer acceptance.

`--post` archives first and rechecks PR head/base and request ordering before posting
one advisory summary. `review finish --post` uses that same path. If publication fails,
the review remains available; retry publication separately. Historical records retain
their original applicability.

## Configuration, scripts, and help

Setup writes `.conjectures/config.json`; add `--global` for user configuration under
`$XDG_CONFIG_HOME/conjectures/` (default `~/.config/conjectures/`). Workspace values
override user values. Other settings and resource limits are preserved. Use your
existing `gh` authentication. `CONJECTURES_GH` may name an executable wrapper, not a
shell command string. Obsolete backend/model settings are ignored with a notice.

Human-readable output is the default. Use `--json` for agents/scripts; output stays
on stdout and progress stays on stderr. JSON retains the recorded outcome and adds
`command_status` and `exit_code`. Plain output contains no terminal escapes.

| Exit | Meaning |
| --- | --- |
| 0 | Operation succeeded: read, prepared complete inputs, queued work, or publication |
| 1 | Failed build, supported review finding, or rejected verification |
| 2 | Invalid input or arguments |
| 3 | Infrastructure/execution error |
| 4 | Required configuration, coverage, or result unavailable |
| 5 | Cancellation or interruption |

Unlike 0.1, successful preparation exits 0 while retaining `awaiting_review` and an
incomplete semantic outcome. Missing sources/builds still exit 4; build failures exit
1. Reading a failed historical run exits 0. Waiting returns the final verification
outcome. Consumers must distinguish command success from the recorded review outcome.

Use `conjectures help review prepare` or any command's `--help` for examples.
Generate shell completion with `conjectures completion bash`, `zsh`, or `fish`; source
the output using your shell's normal completion configuration. No shell files are
changed automatically.

The [release checklist](RELEASE.md) records qualification limits. Upstream roadmap:
[FC #4394](https://github.com/google-deepmind/formal-conjectures/issues/4394).


## Read a retained case

`conjectures run show RUN` displays findings, check outcomes, coverage gaps, and evidence
paths. A fresh applicability observation names changed head/base revisions and its time;
it does not rewrite the original report. `status` lists outstanding work and next commands.
Verification errors leave the policy outcome unevaluated.

To retain additional reviewer context, pass a directory to `review finish --evidence`.
Its optional `reviewer-attributions.json` has `schema_version: fc.reviewer-attribution.v1`,
the existing `request_id`, and a `reviewers` array. Each reviewer records `kind` (`human`
or `ai`), `name`, `method`, `scope` (strings), `independence` (`independent`,
`shared_dependencies`, or `not_assessed`), `shared_dependencies` (strings), and `evidence`
(entries with `path` and `sha256`, relative to that directory). Evidence bytes and request
identity are checked. Attribution and independence remain self-reported, not quality scores
or proof of independent review. The review request/report schemas are unchanged.
