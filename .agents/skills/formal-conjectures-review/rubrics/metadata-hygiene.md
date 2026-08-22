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
declaration records no answer. Raise it as a question, not a finding, unless the PR under
review introduces it — it is a known backlog (#4965 tracks the class), and count the
class in the tree you are reviewing before you say how common it is.

**What a `formal_proof` link shows.** Comparator answers this mechanically where a result
exists — read it and move on. A `comparator.json` in a linked repository is a
configuration file, not a comparator result; check what the workflow actually runs.
Comparator accepts the statement as given, so it replaces none of the other angles.
For the ~330 older links, three things go wrong (all confirmed):

- *The proof assumes something unproved.* A `sorry`-free file can take an unproved result
  as a hypothesis; `#print axioms` does not show it. Erdős 427, 750 and 1141 each linked
  such a proof (Shiu, Stiebitz, Pollack + Mertens); these now use
  `conditional formal_proof ... assuming <decl>` (#4881).
- *The link names no file.* A repo root, commit page or discussion thread shows no file
  to open; a link checker accepts it and a reader finds nothing. 18 links were like this
  (#4895). Finding the proof yourself does not excuse the link: the reader gets the link,
  not your investigation, so a root link stays a finding even when its repository does
  contain the proof — name the exact file and declaration the link should point at.
- *The kind is wrong.* A proof in this repository uses
  `formal_proof using formal_conjectures`; Erdős 316 and 399 linked their own file with
  the wrong kind (#4883).

Examine the declaration, not the file: a `sorry` on some other statement in the same
file is normal.

**Read the automatic checks first, and accept them:**

| Question | Where the answer is |
| --- | --- |
| Does it build? Is it `sorry`-free? | `lake build`, and `hasSorryFreeProof` in the extract |
| Does each statement have `category` and `AMS`? | `extract_names` |
| Is a `research open` statement proved? | the category linter |
| Does the repo agree with erdosproblems.com? | `scripts/check_erdos_status.py` |

If a check fails, report it and stop.

## Not yours

The mathematical content of the statement belongs to source-fidelity and
statement-soundness. Style and format belong to the linters.
