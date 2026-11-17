# Agent guidelines (`palomar_prepare`)

This branch is a clean base for turning a solved problem from
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) into a verified
submission for the [Palomar Registry](https://palomar-registry.org/).

`FormalConjectures/` (the open-problem collection) has been removed. Only the shared libraries
(`FormalConjecturesForMathlib`, `FormalConjecturesUtil`, and `FormalConjecturesTest`), bumped to
Lean / Mathlib `v4.36.0`, plus a placeholder [`formalization.yaml`](formalization.yaml) and
verification scripts in `scripts/`, are present here.

Read [`PALOMAR.md`](PALOMAR.md) and the upstream
[Palomar submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)
when handling edge cases.

---

## End-to-end workflow for creating a Palomar submission

When asked to package a Formal Conjectures problem and its proof for Palomar, execute these steps
in order:

### 1. Locate and audit the original statement

- Retrieve the original problem file (for example via
  `git show origin/main:FormalConjectures/<Source>/<Problem>.lean` if `origin/main` is available)
  and record its commit SHA for `formalization.yaml` (`related_formalizations`).
- Read the cited mathematical source and verify statement fidelity before freezing `Challenge.lean`:
  - Check quantifier order and scope (`∃ x, P x ∧ Q`, never unintended `∃ x, P x → Q`), strict vs
    non-strict bounds, implications, and domain restrictions.
  - Check Lean boundary semantics on empty/smallest inputs (`x / 0 = 0`, `Nat` subtraction
    truncation, `ZMod 0 ≃ ℤ`, `sInf ∅`, sums over empty sets).
  - Document any adaptation, specialization, or divergence honestly in `formalization.yaml`
    (`fidelity.divergences` and `status.scope`) and in `Challenge.lean`.

### 2. Construct `Challenge.lean`

`Challenge.lean` is the small, human-auditable statement contract. Enforce every rule below:

- **Transitive import rule (CRITICAL):** Every file in `Challenge.lean`'s transitive import
  closure **must** belong to Lean core or canonical Mathlib (Tau Ceti / CSLib are flagged as
  qualified dependencies). **Never import `FormalConjecturesUtil` or
  `FormalConjecturesForMathlib` in `Challenge.lean`.**
- **Module header & visibility:** Start the file with `module`, use `public import Mathlib` (or
  targeted `public import Mathlib...` modules), place the `/-! ... -/` module docstring *after*
  the imports, and open `@[expose] public section`.
- **Strip Formal Conjectures attributes:** Remove `@[category ...]`, `@[AMS ...]`,
  `@[formal_proof ...]`, and `@[question ...]`. Translate `@[AMS ...]` codes into
  `classification.msc2020` and `classification.arxiv` in `formalization.yaml`.
- **Inline minimal non-Mathlib definitions:** If the theorem signature uses a definition from
  `FormalConjecturesForMathlib`, copy only that definition (with a precise LaTeX-aware mathematical
  docstring) into `Challenge.lean`. Do not put proof lemmas in `Challenge.lean`.
- **Proof placeholders & size limits:** Write theorem bodies in `Challenge.lean` as `:= by sorry`.
  Keep `Challenge.lean` well within the **1,000-line / 100 KiB** hard limit (target **<= 300 lines
  and <= 32 KiB**; **<= 100 lines** for single-declaration inline rendering).
- **Value questions:** If the problem determines an unknown `<theorem>.answer`, declare
  `def <Namespace>.<theorem>.answer : <Type> := sorry` in `Challenge.lean`, provide the concrete
  definition in `Solution.lean`, list `<Namespace>.<theorem>.answer` in `comparator.json`'s
  `"definition_names"`, and confirm the theorem does not hold vacuously for trivial answers.

### 3. Port the proof into `Solution.lean` (and `Solution/*.lean`)

- **Imports:** `Solution.lean` and submodules under `Solution/` **may** freely `public import`
  from `FormalConjecturesForMathlib`, `FormalConjecturesUtil`, and Mathlib. Do **not** import
  `Challenge` into `Solution.lean`.
- **Exact declaration match:** Every theorem and definition named in `comparator.json` must have
  the **exact same fully-qualified name and kernel type** in `Solution.lean` and `Challenge.lean`.
  If a definition was inlined into `Challenge.lean`, define it identically in `Solution.lean` so
  their types match definitionally; connect it to `FormalConjecturesForMathlib` lemmas by `rfl` if
  helpful.
- **Lean module & file caps:** Every `.lean` file in the repository (except `lakefile.lean`) must
  begin with `module` and have **<= 10,000 physical lines**. Split large proof developments or
  certificates across `Solution/*.lean`. Never create `.lean` symlinks or commit `.olean`/`.ilean`
  files.
- **Axiom hygiene:** Proved declarations may depend **only** on `propext`, `Classical.choice`,
  and `Quot.sound`.
  - Eliminate all `sorry` (`sorryAx`).
  - Replace any `native_decide` (`Lean.ofReduceBool`) with `decide`, `norm_num`, or a
    kernel-checked proof.
  - Never add `axiom`, `opaque`, or `constant`. State unproven mathematical assumptions as
    explicit hypotheses on the theorem in both `Challenge.lean` and `Solution.lean`.
- **Shared library rule:** `FormalConjecturesForMathlib/` must never contain `sorry` or
  `native_decide`. If you add reusable proved lemmas there, run `./scripts/mk_all_formathlib.sh`.

### 4. Update `lakefile.toml` and write `comparator.json`

1. In [`lakefile.toml`](lakefile.toml), add `"Challenge"` and `"Solution"` to `defaultTargets`
   and uncomment the `Challenge` (`warn.sorry = false`) and `Solution` (`globs = ["Solution.*"]`)
   `[[lean_lib]]` sections.
2. If you bump Lean/Mathlib further, ensure `lean-toolchain` matches Mathlib's `lean-toolchain`
   verbatim, verify the Mathlib commit in `lake-manifest.json` is an **ancestor of
   `refs/heads/master`** (never an isolated release-branch patch tag), and commit the updated
   `lake-manifest.json`.
3. Write `comparator.json` at the repository root:
   ```json
   {
     "challenge_module": "Challenge",
     "solution_module": "Solution",
     "theorem_names": ["<Namespace>.<main_theorem>"],
     "definition_names": [],
     "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]
   }
   ```
   Never include `external_kernels` in `comparator.json`.

### 5. Populate `formalization.yaml` and `README.md`

- Replace **every** `TEMPLATE:` sentinel in [`formalization.yaml`](formalization.yaml).
- **Human-only authorship rule:** `project.authors` and `project.responsible_maintainers` are
  strictly for human contributors. Never put an AI model, agent, or tool name in either list.
  Record all AI models, agent frameworks, and prover harnesses accurately under
  `automation.methods`.
- Keep `project.license: "Apache-2.0"` matching the root [`LICENSE`](LICENSE) file.
- Ensure `sources` satisfies Palomar's provenance rule:
  - *Original proof first presented here:* include an entry with `type: original-proof` and
    `relationship: other`, and mark all context/problem sources as `background` or `other`.
  - *Source-based formalization:* omit `type: original-proof` and give at least one source a
    `formalizes`, `adapts`, or `independently-proves` relationship.
  - Allowed `sources[].type` values: `paper`, `book`, `web discussion`, `folklore`,
    `original-proof`, or `other`.
- Rewrite `README.md` into a clear, accurate mathematical summary of the submitted theorem,
  sources, proof structure, and any limitations, suitable for mathematicians and Palomar's
  automated editorial review. Keep the link to `https://submit.palomar-registry.org/` if retaining
  submission instructions.

### 6. Run mechanical verification

Run all checks locally and fix every error and warning before declaring the task complete:

```bash
python3 scripts/check-lean-sources.py --submission
./scripts/mk_all_formathlib.sh
lake --wfail build
lake --wfail test
./scripts/verify-comparator.sh
```

`./scripts/verify-comparator.sh` runs `lake comparator` in `bwrap` and replays the exported proof
through Lean's kernel plus the toolchain's bundled `nanoda_bin` and `con-ron` kernels.

---

## Submitting to Palomar as an agent

If the user explicitly asks you to submit the prepared repository to Palomar, read
<https://submit.palomar-registry.org/llms.txt> first and obey these rules without exception:

1. **Preflight first:** Before calling `POST /api/submit`, run Palomar's complete reusable
   workflow (`PalomarRegistry/PalomarSubmission/.github/workflows/submission.yml` with
   `mode: full` and `execution_profile: palomar-standard-v1`) on the exact 40-character commit SHA
   until the mechanical report returns `status: pass`.
2. **Never drive browser OAuth:** Do not automate the browser form or reuse human web sessions.
   Use only the documented agent protocol (`POST /api/submit` → temporary lightweight git tag
   `palomar-verify-{challenge}` at the commit + secret GitHub gist → `POST /api/verify` → delete
   temporary tag and gist).
3. **Never register without explicit human consent:** Registration on Palomar is permanent and
   append-only. After `GET /api/review` completes, show the full review outcome and findings to
   the user, explain what `POST /register` permanently publishes, and call `POST /register`
   **only** after receiving the user's explicit instruction to register that review.
