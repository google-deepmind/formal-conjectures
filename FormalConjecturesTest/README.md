# FormalConjecturesTest

This directory is the `lake test` driver of the repository. It tests the repository's own
tooling in `FormalConjecturesUtil/`: the `category`, `AMS`, and `formal_proof` attributes, the
`answer( )` elaborator, and the linters.

## What belongs here

- Tests for `FormalConjecturesUtil/`. Mirror its layout: the test for
  `FormalConjecturesUtil/Linters/StubLinter.lean` is
  `FormalConjecturesTest/Util/Linters/StubLinter.lean`.
- Use `#guard_msgs` to check the messages that a linter, attribute, or elaborator produces.

## What does not belong here

- Tests for `FormalConjecturesForMathlib/`. That library is self-contained and follows Mathlib
  conventions. Prove properties of a definition as lemmas in the file that defines it. Put
  sanity checks and `#guard_msgs` tests for notation or elaborators at the end of the file that
  defines them.
- Tests for problem statements. Use a `category test` declaration in the problem file instead.
  See [CONTRIBUTING.md](../CONTRIBUTING.md).

## Running the tests

```bash
lake --wfail test
```

CI runs this command. The library disables `warn.sorry`, so a `sorry` in a test does not fail
the build. Use `sorry` only to construct an input for a linter or attribute test.
