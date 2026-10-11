# Complexity theory

[CircuitLowerBounds.lean](CircuitLowerBounds.lean) states nine lower-bound conjectures
for Boolean families whose truth tables can be printed in time polynomial in `2^n`.
The bounds are `5n`, `50n`, `n log n`, `n log n (log n)^(log log n)`, every fixed
polynomial degree, superpolynomial, `2^(n/2)`, half the Shannon–Lupanov scale, and
asymptotically the full scale. All logarithms are base two.

The definitions use CSLib's deterministic multitape Turing machines and circuits.
There is one construction machine for the entire family. Circuit bounds hold for
all sufficiently large input lengths. For the superpolynomial and near-maximum
statements, the same family works for every exponent or positive error parameter.
The basis is B₂: each of the sixteen binary Boolean operations costs one gate;
inputs and designated outputs are free.

Related statements are the
[nonuniform one-way-function conjecture](../../Books/Goldreich/OneWayFunctions.lean)
and the existing [P versus NP conjectures](../../Millennium/PvsNP.lean).

## Sources and conventions

- Stasys Jukna, [*Boolean Function Complexity*, Chapter 1](https://web.vu.lt/mif/s.jukna/boolean/chapter1.pdf),
  Sections 1.2 and 1.4.1, supplies the circuit conventions and Shannon–Lupanov scale.
  The numerical milestones here are a collection of conjectures using our own
  truth-table explicitness convention. Jukna's Section 1.5.1 instead uses NP
  explicitness, and his page 22 allows infinitely many hard lengths.
- Oded Goldreich, [*Foundations of Cryptography*, Chapter 2 draft](https://www.wisdom.weizmann.ac.il/~oded/PSBookFrag/part2.pdf),
  Sections 2.2.3 and 2.2.5, supplies the length-preserving convention and nonuniform
  strong one-way-function definition (Definition 2.6 in the draft).
- Dylan McKay, Cody Murray, and R. Ryan Williams,
  [*Weak Lower Bounds on Resource-Bounded Compression Imply Strong Separations of Complexity Classes*](https://people.csail.mit.edu/rrw/MCSP-MKTP-stoc19.pdf),
  STOC 2019, supplies the hardness-magnification motivation. Its hypotheses concern
  specified compression problems and computational models. The
  `n log n (log n)^(log log n)` entry is a growth milestone exceeding every fixed
  `n (log n)^c`; a lower bound of this size for an arbitrary explicit family is
  not itself a hardness-magnification theorem.
