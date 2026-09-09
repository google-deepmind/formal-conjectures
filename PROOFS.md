# Proof contributions

Formal Conjectures is mainly a statement repository. Keep proofs short. For a long proof, prefer
an external proof and record it with the `formal_proof` attribute.

Do not add an informal proof of an open research problem.

## Tests and API declarations

Prove a `test` or `API` declaration when the proof is short and useful. A long proof may remain
`by sorry` in `FormalConjectures/`. Do not add a large proof only to remove that placeholder.

For a large computation in a `category test` declaration, `native_decide` may be acceptable.
Review this case by case. Do not use it in `FormalConjecturesForMathlib/`.

## FormalConjecturesForMathlib

Every theorem in `FormalConjecturesForMathlib/` must have a complete kernel-checked proof. Do not
use `sorry`, placeholder definitions, or `native_decide` anywhere in that directory. Keep the code
at Mathlib quality and import only the Mathlib modules that it needs.

## Check proof claims

A file that contains `sorry` can still compile. Before you claim that a theorem is formally
proved, inspect its axioms:

```lean
#print axioms my_theorem
-- [propext, Classical.choice, Quot.sound]
```

`sorryAx` means that the theorem is not proved. Native evaluation can add axioms such as
`Lean.ofReduceBool` or `Lean.trustCompiler`; report them when they are relevant.

For a `formal_proof` link:

1. Open the exact file and declaration that the link cites.
2. Check that the linked statement implies the repository statement.
3. Check for `sorry` and custom axioms.
4. Run `#print axioms` on the linked theorem when the project is available.
5. Use the correct `formal_proof` kind and a stable link.

A repository name, a successful build, or a theorem with a similar name is not enough evidence.
