# EulerBrick

[![CI](https://github.com/PalomarRegistry/EulerBrick/actions/workflows/ci.yml/badge.svg)](https://github.com/PalomarRegistry/EulerBrick/actions/workflows/ci.yml)

A best-practice starting point for a
[Palomar](https://palomar-registry.org/) submission. Use this as a
GitHub template, replace the toy theorem and all `TEMPLATE` metadata, and keep
the separation between the human-auditable statement and the proof.

## Repository map

- `Challenge.lean` is the small statement surface a reader audits.
- `Solution.lean` connects the same declaration to the completed proof.
- `EulerBrick/` contains the full proof development.
- `comparator.json` tells Comparator which declarations must match.
- `formalization.yaml` records the public result description, provenance,
  authorship, automation, fidelity, and review information.
- `LICENSE` contains the Apache License 2.0 terms declared by
  `project.license`.
- `docbuild/` is the recommended nested doc-gen4 project.
- `scripts/verify-comparator.sh` runs pinned Comparator, lean4export, NanoDa,
  and Landrun revisions using the checked-in `comparator.json`, which enables
  the independent NanoDa replay; `scripts/landrun-wrapper.sh` preserves
  lean4export's command delimiter when invoked through Landrun's current CLI
  and refuses any Comparator request to switch off part of the sandbox.

The root uses `lakefile.toml`, a supported stable Lean toolchain, and committed
Lake manifests. The verifier reads `lean-toolchain` and checks that its pinned
lean4export revision targets the same toolchain. When changing that exporter
pin, review whether Comparator and NanoDa remain compatible with its export
format. GitHub Actions builds the Lean project with `lean-action`, generates API
documentation with doc-gen4, and independently checks the advertised statement
with Comparator. Actions and verification tools are pinned to immutable
commits.

## Start a real project

1. Click **Use this template** on GitHub and clone the new repository.
2. Rename `EulerBrick` in the Lake package, module directory, namespace,
   Comparator declaration, and metadata.
3. Replace the example library, `Challenge.lean`, and `Solution.lean`.
   Keep `Challenge.lean` as the small statement-only surface, with one `sorry`
   for each advertised declaration; put the proofs in `Solution.lean`, where
   Comparator checks them against those statements. The proof-status counts in
   `formalization.yaml` exclude the deliberate Challenge `sorry`s.
4. Replace every `TEMPLATE` value in `formalization.yaml`. Values that might
   otherwise look like plausible defaults—including repository role,
   classifications, proof counts, automation method, and review status—are
   deliberately invalid until you choose them. Replace a placeholder list with
   an empty list only where its adjacent comment permits that; lists described
   as required must remain nonempty.
   Write `project.description` as the concise public registry abstract for the
   formalization as a whole. It should let a mathematical reader identify the
   subject and principal result families; it is not an inventory of Comparator
   declarations, and the README and Challenge documentation can carry the
   fuller account. `status.main_results` is optional: add it only when a short
   curated project-level list is useful, not to mirror Comparator declarations.
   The `sources` list must remain nonempty. Every source relationship must be
   exactly `formalizes`, `adapts`, `independently-proves`, `background`, or
   `other`. Choose one result origin: for a result first presented by the
   formalization, include a descriptive source with `type: original-proof` and
   `relationship: other`; every additional source must use `background` or
   `other`. Otherwise, omit `type: original-proof`, and give at least one cited
   mathematical source a `formalizes`, `adapts`, or `independently-proves`
   relationship. A new proof of a known published result is source-based and
   uses `independently-proves`, not `original-proof`.

   Every source needs a title and relationship. Its `type`, authors,
   contributors, identifier, location, licence, and endorsement may be removed
   when genuinely inapplicable. Use authors only for bibliographic authorship;
   use contributors with a name and free-form role for credits such as editors
   and problem proposers. A retained type is a concise free-text description
   such as `article`, `paper`, `book`, `formalization`, `web post`,
   `folklore`, or `conversation`. The exact value `original-proof` is
   reserved for the result-origin declaration above. Set
   `repository.role` to `substantive-development` and omit
   `substantive_formalization`, or set it to `thin-wrapper` and provide the
   underlying `owner/repository` or `https://github.com/owner/repository` URL
   plus its full 40-character lowercase commit SHA. Remove
   `related_formalizations` or set it to `[]` when none are known.
   Keep the repository's Apache-2.0 `LICENSE` file and the matching
   `project.license: "Apache-2.0"` metadata. This starter template supports
   only that root licence. If the project deliberately uses another root
   licence permitted by Palomar policy, use another starting point or own and
   maintain the project's licence-validation CI contract. Cited sources and
   dependencies retain their own licences.
5. Update and commit dependency pins:

   Before fetching and building the dependency closure, budget several GiB of
   free space. After the root cache fetch and build, a clean local checkout of
   the template's pinned Lean v4.32.0 manifest occupied about 7.7 GiB across
   about 123,000 files under `.lake/`. The documentation build adds doc-gen4 and
   its dependency closure under the shared `.lake/packages/` plus generated
   output under `docbuild/.lake/`. The precise footprint changes with the
   filesystem, cache contents, and any dependency updates. Both `.lake/`
   directories are generated and must not be committed.

   ```text
   lake update
   (cd docbuild && MATHLIB_NO_CACHE_ON_UPDATE=1 lake update)
   ```

6. Run the project checks before submitting:

   ```text
   lake exe cache get
   lake build
   (cd docbuild && lake build EulerBrick:docs)
   ruby scripts/validate-formalization.rb
   ./scripts/verify-comparator.sh
   ```

   The metadata command parses the YAML, requires the Apache-2.0 root-licence
   declaration, and reports the path of every retained template sentinel. CI
   also detects the checked-in `LICENSE` file independently and runs an
   explicit `--expect-template` check only in the canonical
   `PalomarRegistry/EulerBrick` repository, proving that the shipped toy
   metadata still has exactly the intended sentinel surface. Pull requests
   from contribution forks run in that upstream repository context. Every
   other repository—including standalone forks and repositories made with
   **Use this template**—runs the ordinary command and requires every sentinel
   to be replaced. CI also runs the corresponding build, documentation, cache,
   and Comparator checks. Run the final command from the repository root. The
   full check set requires Linux, Git, Go, Ruby, Rust/Cargo, Python 3, and a
   working Landrun sandbox.

   The pinned `lean-action` likewise runs `lake exe cache get` in CI and caches
   `.lake/`. A successful canonical starter run deliberately includes the
   statement-surface `sorry` warning and demonstrates the wiring, not submission
   completeness.

7. Read the current
   [Palomar submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md),
   commit the final snapshot, and
   [open the submission form](https://submit.palomar-registry.org/)
   with the full 40-character commit SHA.

   Submit only if you are a responsible author or maintainer of the substantive
   formalization, or have approval from one. For a thin wrapper, answer about
   the underlying formalization rather than the wrapper; the form records that
   relationship and allows optional evidence.

## Important boundaries

This repository is structurally valid but its toy theorem does **not** meet
Palomar's editorial floor. A green build or Comparator check establishes only
that Lean accepts the project and that the recorded solution proves the recorded
statement using the permitted axioms. It does not establish mathematical
significance, fidelity to a source, novelty, or peer review.

Keep `Challenge.lean` ordinary and readable. Definitions needed by the statement
must have precise mathematical meanings and docstrings. Its transitive imports
must resolve to Lean core, Mathlib, Tau Ceti, or CSLib; a Tau Ceti or CSLib
import enlarges the trust surface and is prominently flagged. Dependencies used
only by the proof may be arbitrary pinned Git dependencies.
The root licence covers this repository snapshot only; cited papers, reused
formalizations, and dependencies retain their own licences.

Questions are welcome in the
[Palomar channel on the Lean Zulip](https://leanprover.zulipchat.com/#narrow/channel/621638-Palomar).
