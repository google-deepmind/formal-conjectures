# Use proof-verification evidence

Comparator checks a submission against a specified formal statement and permitted axioms.
The review skill checks source fidelity, hypotheses and answer meaning. A pass in one does
not establish the other. Follow the repository's `PROOFS.md` for `formal_proof` claims.

## Check what the result covers

Before relying on an existing result, inspect evidence from the trusted verification workflow:

- **Statement:** FC repository, immutable commit, module and declaration. Check any exported
  challenge digest against the artifact actually verified.
- **Proof:** repository, immutable commit, exact declaration and any bridge deriving the FC
  statement from it. The bridge and generated workspace must also be identified by revision
  or content digest.
- **Environment:** Lean and dependency pins, exporter/generator/verifier versions, kernel
  checks and permitted-axiom policy. A pass under extra assumptions is not an unconditional proof.
- **Outcome:** the recorded result and supporting artifacts must cover those inputs. A config
  file, reachable URL or successful project build is not a verification result.

A result for different inputs is historical evidence. Do not silently reuse it for the current
claim. A workflow may establish that the relevant inputs are unchanged, but the skill should
not guess that from similar names or a small diff.

## Route missing verification

For a supplied Lean proof without matching evidence, identify the exact target and request or
invoke the available verification workflow within the task's authorization. Its path is:

FC statement → exporter → shared generator → pinned submission and bridge → Comparator.

Use the workflow's documented interface. If it is unavailable, record verification as **not
run** and the missing step. This skill does not require every deployment to have an exporter,
Comparator or a registry installed. Proofs in another formal system need that system's
verification path; do not present them as Comparator-verified.

The skill may propose a bridge, but the verifier must check it independently. Keep the trusted
challenge, dependency policy and axiom policy outside the submission's control. Build and run
external proof code only through the isolated verification workflow; a Git worktree is not a
sandbox. See [Comparator's trust assumptions](https://github.com/leanprover/comparator#comparator).

## Report the result without extending it

Keep proof verification separate from the semantic verdict:

- **Verified under the named policy:** matching evidence confirms success.
- **Rejected:** the verifier reports that the submitted claim fails its checks; retain the reason.
- **Error:** execution or infrastructure failed; this says nothing about proof correctness.
- **Not run:** matching verification has not completed or is unavailable.
- **Not applicable:** no proof claim is in scope.

Use structured tool results where available and preserve their evidence references. A nonzero
exit alone does not distinguish rejection from an infrastructure error. Without a documented
distinction, report an error with diagnostics; do not classify it by matching log text.

Read the theorem's hypotheses as well as its axiom closure. A theorem proving `H → P` does not
establish `P` without `H`. Check that conditional proof metadata states the actual relationship.
Definition-hole answers also need a meaning check: restating the unknown in its own answer can
pass kernel checks without solving the problem. Neither a proof pass nor an advisory review
authorizes a merge or a status change.
