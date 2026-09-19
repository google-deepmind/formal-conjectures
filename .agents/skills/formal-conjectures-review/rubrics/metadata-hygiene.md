# Metadata hygiene

Your job: whether the declaration's metadata — category, status, and `formal_proof`
claims — matches what the statement and its source actually establish. The tags drive
what downstream consumers (the website, the LeanEval import, comparator configs) believe
about a statement, so a wrong tag propagates further than a wrong word. This angle may
block.

## What to hunt for

**Category against status.** Does the category of each declaration — and each variant —
match its actual status? A statement whose content is settled in the file or the source
must not sit under `research open`; a `test` statement asserting research content is the
same defect reversed. The category linter warns when a `research open` statement is
*proved*; it cannot know what the source considers settled — that part is yours.

**Unfilled slots under `research solved`.** A `sorry` in the *proof* of a
`research solved` declaration records a known result and is sanctioned. An unfilled
`answer(sorry)` *slot* under `research solved` is different: `CONTRIBUTING.md` says the
slot "should be replaced by `answer(True)` or `answer(False)`", so until then the
declaration records no answer. For a PR review, distinguish introduced or changed slots from
pre-existing ones. Report an actionable discrepancy in scope; do not turn unrelated unfinished
answers into a backlog survey. Follow the repository's current answer policy.

**What a `formal_proof` link shows.** Read any existing verification evidence first. Follow
[`../references/verifying-proofs.md`](../references/verifying-proofs.md) to check its statement,
proof and bridge revisions, verifier policy and outcome. A `comparator.json` is configuration,
not a result. A pass applies only to the recorded inputs and permitted axioms; it does not
settle source fidelity or whether an answer is meaningful. Check these relationships:

- *The proof assumes something unproved.* A `sorry`-free file can take an unproved result
  as a hypothesis; `#print axioms` does not show it. Check that the actual hypotheses are
  represented by the conditional-proof metadata required by `PROOFS.md`.
- *The proof cannot be located reproducibly.* Inspect what the link and accompanying metadata
  identify under `PROOFS.md`. A reachable repository or discussion page alone is not verification.
  When the locator is insufficient, explain what is missing and give the exact file, declaration
  and revision if established. Do not infer an invalid proof solely from the URL's shape.
- *The kind is wrong.* A proof in this repository uses
  `formal_proof using formal_conjectures`; check the linked proof's actual location and system.

Examine the declaration, not the file: a `sorry` on some other statement in the same
file is normal.

**Read automatic checks for the reviewed revision first:**

| Question | Where the answer is |
| --- | --- |
| Does it build? | Focused `lake --wfail build` or matching CI evidence |
| Does the in-repository declaration have a `sorry`-free proof? | `hasSorryFreeProof` in the extract; this does not verify an external link or establish its full axiom policy |
| Does each statement have `category` and `AMS`? | `extract_names` |
| Is a `research open` statement proved? | the category linter |
| Does the repo agree with erdosproblems.com? | `scripts/check_erdos_status.py` |

Record failed, unavailable or stale checks separately. Do not turn a tool error into a
semantic finding, or unavailable evidence into a pass. A blocked required check makes the
review INCOMPLETE unless an established defect already requires revision.

## Not yours

The mathematical content of the statement belongs to source-fidelity and
statement-soundness. Style and format belong to the linters.
