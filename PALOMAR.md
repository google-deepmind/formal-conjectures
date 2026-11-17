# Preparing a Palomar Submission from Formal Conjectures

This guide explains how to turn a formal proof of a problem from
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) into a verified
submission for the [Palomar Registry](https://palomar-registry.org/).

## Why this branch exists

In `google-deepmind/formal-conjectures`, open problems live in `FormalConjectures/` and import
`FormalConjecturesUtil` and `FormalConjecturesForMathlib`. Long research proofs are hosted in
dedicated repositories and registered on [Palomar](https://palomar-registry.org/), then linked
back via `@[formal_proof ...]`.

The `palomar_prepare` branch gives you a clean starting point for that proof repository:

- Problem statements (`FormalConjectures/`), website code (`site/`), and documentation-build
  machinery (`docbuild/`) are removed.
- `FormalConjecturesForMathlib`, `FormalConjecturesUtil`, and `FormalConjecturesTest` are kept
  and already bumped to a Palomar-compatible Lean and Mathlib version (`leanprover/lean4:v4.36.0`).
- A ready-to-fill [`formalization.yaml`](formalization.yaml) (`v0.4`) template and local
  verification scripts (`scripts/check-lean-sources.py`, `scripts/verify-comparator.sh`) are
  included.

---

## Step-by-step workflow

### 1. Create a public repository from `palomar_prepare`

Start a new branch or repository from `palomar_prepare` and fetch the prebuilt Mathlib cache:

```bash
lake exe cache get
lake --wfail build
```

If you need a newer Lean/Mathlib version than the one pinned here:

1. Update `lean-toolchain` and the `mathlib` `rev` in `lakefile.toml` together so `lean-toolchain`
   matches the exact `lean-toolchain` of the resolved Mathlib commit.
2. **Ensure the Mathlib commit is an ancestor of `refs/heads/master`** in
   `leanprover-community/mathlib4` (avoid isolated patch-release tags on release branches that
   were never merged back into `master`, as Palomar's mechanical verifier rejects them).
3. Run `lake update && lake exe cache get` and commit the updated `lake-manifest.json`.

### 2. Create `Challenge.lean` (the human-auditable statement)

Inspect the original problem file from `main` (for example
`git show origin/main:FormalConjectures/ErdosProblems/123.lean`) and port the solved statement
into a root `Challenge.lean` file.

**Strict Palomar requirements for `Challenge.lean`:**

- **Mathlib-only transitive imports:** Every file in `Challenge.lean`'s transitive import closure
  must come from Lean core or canonical Mathlib (Tau Ceti and CSLib are permitted only as
  qualified dependencies). **`Challenge.lean` must NOT import `FormalConjecturesUtil` or
  `FormalConjecturesForMathlib`.**
- **Strip Formal Conjectures attributes:** Remove `@[category ...]`, `@[AMS ...]`,
  `@[formal_proof ...]`, and `@[question ...]`. Record subject classifications and provenance in
  `formalization.yaml` instead.
- **Inline minimal non-Mathlib definitions:** If the statement depends on a definition from
  `FormalConjecturesForMathlib`, copy only the minimal definition (with a precise mathematical
  docstring) into `Challenge.lean` inside `@[expose] public section`. Keep lemmas and proofs out
  of `Challenge.lean`.
- **Use Lean's module system and keep it short:** Start with `module`, put the module docstring
  after imports, and end each advertised theorem with `:= by sorry`. Hard limits are **1,000
  lines and 100 KiB** (aim for under 300 lines and 32 KiB; single-theorem files under 100 lines
  render inline on Palomar).

Example `Challenge.lean`:

```lean
module

public import Mathlib

@[expose] public section

/-!
# Erdős Problem 123

Plain-language mathematical context, cited source, and explanation of any definitions or
boundary conditions.
-/

namespace Erdos123

/-- Concise mathematical statement of the result, matching the cited source. -/
theorem erdos_123 : True := by
  sorry

end Erdos123
```

**Value questions (`answer(...)`):** If the original Formal Conjectures statement asks for a
value via `<theorem>.answer := sorry`:

1. Declare `def MyNamespace.my_theorem.answer : <Type> := sorry` in `Challenge.lean` before the
   theorem.
2. Supply the concrete definition body in `Solution.lean`.
3. Add `"MyNamespace.my_theorem.answer"` to `"definition_names"` in `comparator.json`.
4. Verify that the theorem genuinely constrains the answer and is not vacuous for arbitrary values.

### 3. Add the proof in `Solution.lean` (and optional `Solution/*.lean` modules)

Create `Solution.lean` at the repository root (plus any supporting modules under `Solution/`).

- **Imports:** Unlike `Challenge.lean`, `Solution.lean` **may** freely `public import` modules
  from `FormalConjecturesForMathlib`, `FormalConjecturesUtil`, `Solution.*`, or other pinned
  public GitHub dependencies. Do **not** import `Challenge` from `Solution.lean`; Comparator
  compiles them separately and compares exported kernel declarations.
- **Matching signatures:** Every declaration listed in `comparator.json` must appear in
  `Solution.lean` with the **exact same fully-qualified name and type** as in `Challenge.lean`.
  If you inlined a definition `Foo` in `Challenge.lean` that also exists in
  `FormalConjecturesForMathlib`, define `Foo` identically in `Solution.lean` (you can bridge to
  `FormalConjecturesForMathlib`'s lemmas by `rfl` or unfolding).
- **Module & file-size rules:** Every `.lean` file in the repository must start with `module`
  and contain **at most 10,000 physical lines**. Split large proofs or generated certificates
  across submodules under `Solution/`. Never commit `.lean` symlinks or compiled `.olean` files.
- **Permitted axioms only:** Proved declarations may depend only on `propext`,
  `Classical.choice`, and `Quot.sound`. Neither `sorry` (`sorryAx`) nor `native_decide`
  (`Lean.ofReduceBool`) is permitted; use kernel-checked `decide` or reflection proofs instead.
  If the proof is conditional on an unproved hypothesis (e.g. `RiemannHypothesis`), make it an
  explicit parameter of the theorem in both `Challenge.lean` and `Solution.lean` rather than an
  `axiom`.

Check axioms in Lean before finishing:

```lean
#print axioms Erdos123.erdos_123
```

### 4. Enable `Challenge` and `Solution` in `lakefile.toml` and add `comparator.json`

1. In [`lakefile.toml`](lakefile.toml):
   - Add `"Challenge"` and `"Solution"` to `defaultTargets`.
   - Uncomment the `[[lean_lib]]` blocks for `Challenge` and `Solution` at the bottom of the file.
2. Create `comparator.json` at the repository root:

```json
{
  "challenge_module": "Challenge",
  "solution_module": "Solution",
  "theorem_names": ["Erdos123.erdos_123"],
  "definition_names": [],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]
}
```

Do **not** add an `external_kernels` key to `comparator.json`; Palomar rejects it as a submitter
field and injects its own bundled `nanoda` and `con-ron` kernel configurations.

### 5. Fill in `formalization.yaml` and update `README.md`

1. Edit [`formalization.yaml`](formalization.yaml) and replace **every** `TEMPLATE:` value:
   - **`project.authors` and `project.responsible_maintainers`:** List **human** names only.
     Credit AI models, provers, and agents in `automation.methods`.
   - **`project.license`:** Keep `"Apache-2.0"` in sync with the root [`LICENSE`](LICENSE) file.
   - **`classification`:** Provide 1–8 official arXiv subject categories (e.g. `math.NT`) and
     up to 8 MSC2020 codes (translate `@[AMS ...]` numbers from the original problem file).
   - **`sources`:** Choose either **original** mode (one entry with `type: original-proof` and
     `relationship: other`, plus any problem-list/context sources as `background` or `other`) or
     **source-based** mode (no `original-proof`, and at least one mathematical source with
     `formalizes`, `adapts`, or `independently-proves`). When `type` is present, use only
     `paper`, `book`, `web discussion`, `folklore`, `original-proof`, or `other`.
   - **`related_formalizations`:** Fill in the note linking the exact Formal Conjectures module
     and commit SHA where the formalized conjecture originated.
2. Update [`README.md`](README.md) so it clearly describes the mathematical theorem, proof
   overview, sources, and any scope limitations or divergences for human readers and Palomar's
   editorial review.

### 6. Verify locally and submit to Palomar

Run the local checks from the repository root (requires Linux and `bwrap` / `bubblewrap` for
`lake comparator`'s sandbox):

```bash
python3 scripts/check-lean-sources.py --submission
lake --wfail build
lake --wfail test
./scripts/verify-comparator.sh
```

Optionally validate `formalization.yaml` against the upstream JSON schema:

```bash
check-jsonschema --schemafile https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/main/schema/formalization.schema.json formalization.yaml
```

When everything passes:

1. Commit all changes and push to a **public GitHub repository**.
2. Record the full 40-character commit SHA: `git rev-parse HEAD`.
3. Follow the [Palomar submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)
   (including running Palomar's reusable preflight workflow if desired) and submit the repository
   and 40-character SHA at <https://submit.palomar-registry.org/>.
4. Once registered, open a PR on `google-deepmind/formal-conjectures` (`main`) updating the
   problem's category to `@[category research solved]` and linking the permanent `PALOMAR-...`
   entry with `@[formal_proof ...]`.
