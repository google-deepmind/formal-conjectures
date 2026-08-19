# Defect classes

This is the reference for the `review` skill. `SKILL.md` gives the procedure. This
file gives the classes of defect that the procedure looks for, each with an example from this
repository.

It answers one question: does the Lean statement say what the source says? `AGENTS.md` covers
the mechanical pass. This covers the part that needs judgement.

A tool such as `leanprover/comparator` decides whether a submitted proof establishes a given
statement, under a permitted set of axioms. That question is mechanical, and it is being automated.
This guide is about the other question. No checker settles it, because every checker takes the
statement as given. Thus the automated side gets better, and this side becomes more important.

## What this pass gives

This pass gives **recommendations**. It does not decide whether to merge a pull request. The
contributor can disagree with a finding, and can ask a maintainer to decide.

Each finding must carry a **witness**. A witness is a concrete case where the Lean and the source
disagree. Then a reader can check the finding without doing the review again.

- "This looks too strong" is not a finding.
- "At `c = 2` and `n = 100` the hypothesis needs 20000 edges, and a simple graph has at most 4950"
  is a finding.

## Read the automatic checks first

Do not examine what a script decides already. Read these results first, and accept them:

| Question | Where the answer is |
| --- | --- |
| Does it build? Is it `sorry`-free? | `lake build`, and `hasSorryFreeProof` in the extract |
| Does each statement have `category` and `AMS`? | `extract_names` |
| Is a `research open` statement proved? | the category linter warns about this |
| Does the repo agree with erdosproblems.com? | `scripts/check_erdos_status.py` |

If a check fails, report it and stop. Do not review the mathematics of a file that does not build.

## The checks that need judgement

Each item below is a class of defect from this repository.

Examples are marked **confirmed** or **lead**. A confirmed example has a witness that somebody
checked. A lead is a place to look. Do not report a lead as a finding.

A confirmed example may since have been fixed, and several here have open pull requests against
them. That does not weaken the example: the shape is the lesson, not the current state of the
file. But do not go looking for the defect in the tree and conclude the entry is wrong, and do
not re-report one whose fix is already open. The pull request is named where there is one.

### 1. The statement does not match the source

Read the source. Do not read only the docstring, because the docstring is also under review.

Compare the quantifiers, the direction of each inequality, the constants and the ranges. A reversed
conclusion is easy to miss, because the Lean reads well in both directions.

Sometimes you do not need the paper. The docstring records the source, so a statement can
contradict its own file.

- *Erdős 887* `variants.rosenfeld_4` (confirmed): the docstring gives the interval as
  `(n^{1/2}, n^{1/2} + n^{1/4})`, where the coefficient is `1`. The Lean writes
  `∃ C > 0, ... C * n^(1/4)`. The two give different answers for the greatest `K`. One of them is
  wrong, and either way the file disagrees with itself.

Check that first, because it is cheap. These leads need the cited papers, and they are open in
#4896:

- *(unnamed, because it is a case in `evals/`)*: a file states an extremal value as an equality
  where the source asks whether that value is eventually unattainable. The pigeonhole half is
  already a theorem in the same file, so the open content is the other half. Fixed in #4941.
- *Erdős 757*: `IsAdmissible` may use `(B - B).ncard = 11`, where the source has `11 ≤`.
- *Erdős 1167*: the module docstring records the condition `κ α > r`. The theorem may omit it.

### 2. The hypotheses cannot hold

A statement with unsatisfiable hypotheses is true, and says nothing. The file builds, and the
statement has a correct type. Thus no automatic check finds this.

For each hypothesis, ask what must exist. Then ask whether such a thing exists.

Look also at total functions. Lean functions are total, so a definition can return a default value
outside its intended domain. `sInf ∅ = 0` is the one that occurs here. The statement is then about
the default value, and not about the mathematics.

- *Erdős 80* (confirmed): `Admissible c G` required `c * n ^ 2 ≤ #G.edgeFinset`. A simple graph on
  `n` vertices has at most `n * (n - 1) / 2` edges. At `c = 2` and `n = 100`, that is 20000 against
  4950. For `c ≥ 1/2` no graph qualifies. The set is empty, `sInf ∅ = 0`, and both `research open`
  statements were false. See #4867 and #4877.
- *Erdős 694* (confirmed): the hypothesis is `∀ n, IsGreatest (Nat.totient ⁻¹' {n}) (fmax n)`, over
  each `n : ℕ`, and `IsGreatest S a` requires `a ∈ S`. But `φ(m)` is even for each `m > 2`, and
  `φ(1) = φ(2) = 1`. Thus `3` is a nontotient and the fibre over `3` is empty. No `fmax` satisfies
  the hypothesis. Note that the conclusion already restricts `n` to the range of `φ`. The
  hypothesis needs the same restriction. See #4896.

A junk value is not a defect by itself. Both examples above are defects because a statement
turned out to be *about* the junk value. Ask instead what reads the definition, and whether any
of it can reach the degenerate input.

So the question is never "does this definition have a junk value", which many do. It is whether
anything reads it at the degenerate input, and whether reaching it can change a claim. Enumerate
every declaration that uses the definition and say what the junk does to each. That table is the
answer to the report, and it is the deliverable when the answer turns out to be "nothing breaks".

Three rules of thumb, and one caveat that undoes the first. A junk value of `0` at the bottom of
`ℕ` can only make an *upper* bound easier, and is dangerous only for a lower bound, an exact
value, or a `≠ 0` claim. The caveat: that holds where the junk sits in a *bound*. Where it sits in
the admissibility predicate of an `∃ a, Admissible a ∧ P a`, it makes the existential easier to
witness, so it strengthens rather than weakens, and can decide a `research open` answer. A parameter
left free at finitely many inputs absorbs any junk value there. And an `=O` or `=o` statement at
`atTop` cannot see finitely many inputs at all.

When the source states a restriction that the docstring drops, and the junk value is what makes
the omission observable, that is a finding against the docstring rather than against any
statement.

### 3. Boundary cases

Examine the smallest value of each bound.

- *(confirmed; unnamed, because it is a case in `evals/`)*: a variant quantifies from one below
  the bound its source states. At that value it asserts a set is cofinite, while a `research
  solved` statement in the same file gives the same set density `0`. Both cannot hold, so the
  answer slot on a `research open` statement is already decided, for a value the source excludes.
  Two statements in one file contradicting each other is the cheapest boundary defect to find and
  the easiest to read past. Fixed in #4933.
- *Green 21* (confirmed): `fox_kleitman_modular` permits `k = 0`. The hypothesis then holds
  vacuously, and the conclusion becomes `(0 : ZMod p) ≠ 0`. Thus no `f` exists, and the answer is
  `False` for a reason that has nothing to do with the question.
- *Erdős 939* (confirmed, but weaker than it appears): `Nat.Full k n` is
  `∀ p ∈ n.primeFactors, p ^ k ∣ n`, and `primeFactors 0 = ∅`. Thus `0` and `1` are Full, and
  `{0, 1} ∈ Erdos939Sums 4`. Fixed in #4934. But the theorem quantifies over each `r ≥ 4`. At `r = 5` a member
  needs three elements, and `{0, 1, x}` then needs `x` and `x + 1` both 5-full, which nobody
  has exhibited. The witness settles one case only.

  Note that `0` is not what blocks `r = 5`. `Finset.Coprime S` is `S.gcd id = 1`, the gcd of
  the whole set, so `{0, 1, x}` is coprime for every `x`. An earlier version of this file said
  that a coprime set cannot contain `0`, which is wrong. Read the definition before you reason
  about it.

Use the last example as the model. Report what the witness shows, and also what it does not show.
A finding that claims too much costs the reviewer more time than no finding.

### 4. `answer()` semantics

`answer(sorry)` marks the unknown part of the problem.

**Polarity.** `answer(True) ↔ P` and `answer(False) ↔ P` are opposite claims. Compare the answer
with the source first.

**Self-answer.** An `answer` term can sometimes take the value that it must determine. The
statement is then provable by `rfl`, and it settles nothing. *Erdős 195* (confirmed) is
`answer(sorry) = sSup S`, so the slot accepts `sSup S`. `AGENTS.md` states that a tautological
answer is not a solution. No check enforces that.

**Scope.** An `answer` inside a binder makes a different claim from one outside it. `AGENTS.md`
requires the quantifiers to come after `answer(sorry)`.

`answer(sorry) ↔ ∀ᵉ ...`, with the binders written inside the iff, is the sanctioned shape, and
not a defect. `FormalConjecturesUtil/Linters/AnswerLinter.lean` recommends it. Do not report it.

A section `variable` above the declaration is the opposite case and is blocking. The elaborated
statement becomes `∀ {n}, answer(sorry) ↔ P n`, and one Prop cannot be equivalent to `P n` at
every `n`: where the source's `P` is vacuous at some `n` the slot is forced to `True`, so
`answer(False)` is unstatable and the problem can never be resolved negatively. The linter does
not see section variables, so CI catches nothing. Read the binders off the elaborated statement
and check the `variable` declarations at the top of the file. *LatinSquare* (confirmed):
`oddOrderLatinSquareTransversal` and `latinSquareNearTransversal` both picked up `variable {n : ℕ}`;
`Odd n → …` is vacuous at even `n`. See #5009 and #5060, and #1407 for the linter blind spot.

**A `sorry` proof and an unfilled slot are different.** A `sorry` in the *proof* of a
`research solved` declaration records a result known in the literature and is sanctioned. An
unfilled `answer(sorry)` *slot* under `research solved` is a separate thing: `CONTRIBUTING.md`
says that once the problem is solved the slot "should be replaced by `answer(True)` or
`answer(False)` accordingly", so until it is, the declaration records no answer. *LatinSquare*
`oddOrderLeq9LatinSquareTransversal` is one.

Raise it as a question, not a finding, unless the pull request under review introduces it. It is
a known backlog rather than a per-PR defect: 13 of the 349 `research solved` declarations that
use `answer(...)` still carry `answer(sorry)`, and #4965 is open to fix the class. Count it in
the tree you are reviewing before you say how common it is.

- *Erdős 887* `parts.i` (confirmed): the slot sits inside the binders for `C` and `n`, so it
  accepts the left side and `le_refl` closes the statement. `parts.i` and `parts.ii` carry the same
  docstring, which asks for "an absolute constant `K`". Only `parts.ii`, which writes
  `∃ K, ∀ C > 0, ...`, states that. See #4896.

### 5. What a `formal_proof` link shows, before comparator

This section is temporary. Comparator answers this question mechanically. It builds a submitted
proof in a sandbox, it checks that the proof establishes the trusted statement, and it enforces a
list of permitted axioms. Read the comparator result where one exists, and go to the next section.

A `comparator.json` in the linked repository is not a comparator result. It is a configuration
file, and the repository's CI may only run a plain build. Check what the workflow actually runs
before you treat the link as mechanically verified.

Comparator does not replace sections 1 to 4. It accepts the statement as given. A machine-checked
proof of a wrong statement is a machine-checked proof of the wrong thing.

About 330 links in the repository are older than any of this. Each link claims that a proof of the
statement exists. Three things go wrong.

**The proof assumes something unproved** (confirmed). A file can be `sorry`-free, and can still
need an axiom that the author declared. `#print axioms` does not show this, because the proof takes
the assumption as a hypothesis. Erdős 427, 750 and 1141 each link such a proof. The assumed results
are Shiu's theorem, Stiebitz's theorem, and Pollack's Theorem 1.3 with Mertens' third theorem.
These now use `conditional formal_proof ... assuming <decl>`. That clause names the assumption as a
Lean declaration, and a list of permitted axioms does not. See #4881.

**The link does not name a file** (confirmed). A repository root, a commit page or a discussion
thread does not show which file to open. No check can read such a link. 18 links were like this.
One pointed at `FormalizedFormalLogic/Foundation`, which holds no modal logic. A link checker
accepts that link, and a reader finds nothing. See #4895.

**The kind is wrong** (confirmed). A proof in this repository uses
`formal_proof using formal_conjectures at ""`. Erdős 316 and 399 each linked their own file
instead. See #4883.

Examine the declaration, and not the file. A `sorry` on some other statement in the same file is
normal.

### 6. Variants

A variant makes a claim about the same problem, so apply the same checks. Then ask two more
questions. Does the category of the variant match its status? Does a shared definition make the
variant stronger or weaker than its docstring says? A defect in a shared definition affects each
statement in the file.

## How to report

Give concrete findings. Do not give a score. For each finding, give:

- the declaration and the line
- what the source says, with a locator
- what the Lean says
- the witness
- a suggested change, if you have one

Then give one verdict:

- **CLEAN**: no findings.
- **ACCEPT WITH NITS**: the findings do not change the meaning of the statement.
- **NEEDS REVISION**: at least one finding changes the meaning, or makes the statement vacuous, or
  shows that a `formal_proof` claims more than the linked proof gives.

The verdict is advice about the statement. It is not a decision about the merge, and it is not a
judgement about the contributor.

## Out of scope

Do not report these:

- style, naming and format, which `AGENTS.md` and the linters cover
- a shorter proof for a `test` or `API` statement that builds
- a different but equivalent formalisation, unless the difference is observable
- whether the conjecture is true
- whether to merge the pull request

## Uncertainty

Report your confidence. If you cannot give a witness, write the item as a question. #4896 is the
model: it marks its contents as leads, and not as confirmed bugs.

## Prior art

This guide cites the work below. It does not copy from it, because
[ryantuck/erdos-ai](https://github.com/ryantuck/erdos-ai) has no licence, and this repository needs
the CLA. @ryantuck can contribute any of that work himself.

- [`FABLE_REVIEW.md`](https://github.com/ryantuck/erdos-ai/blob/master/FABLE_REVIEW.md), which names
  the recurring failure modes, and which reviews the previous review
- [`ryantuck/formal-conjectures#1`](https://github.com/ryantuck/formal-conjectures/pull/1), an
  example of this pass on Erdős 7, raised here by @franzhusch
- the verdicts that @bocowgill suggested in #4876
- the audit by @KitaKen1 in #4896, which is the source of the leads above
