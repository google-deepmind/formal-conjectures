# BES — Brahim-Erdős-Straus Lean 4 Formalization

Formalizes the 4 TIGHT theorems from the BES conjecture register as
machine-checkable proofs.

## Theorems

| ID | Statement | File | Tactic |
|---|---|---|---|
| BES-3  | $G(214) = 8 = 2^{N_c}$ | `Bes/GoldbachAnchor.lean` | `native_decide` |
| BES-11 | $H_{840} = QR((\mathbb{Z}/840)^*)$ | `Bes/Mordell.lean` | `native_decide` |
| BES-12 | $\Pi_{\text{Heeg}} = -QR((\mathbb{Z}/840)^*)$ | `Bes/PiHeeg.lean` | `native_decide` |
| BES-13 | Frobenius $x \to x^{29}$ involution preserving both | `Bes/Frobenius.lean` | `native_decide` |

All theorems are finite and decidable. `native_decide` compiles to native code
for fast evaluation; useful when `decide` would be slow on 840-element ZMod
or 840+-prime Goldbach computation.

## Build

```bash
elan toolchain install leanprover/lean4:v4.13.0  # if not installed
lake update                                        # fetch mathlib
lake build                                         # compile all theorems
```

If `native_decide` is too slow on your machine, fall back to `decide` (slower
but doesn't require the C compiler bridge).

## Verification status

The mathematical content of every theorem has been verified by independent
Python computation. The Lean proofs are sound under the assumption that
`native_decide` correctly reflects the decidable instance — which it does for
`ZMod`, `Nat.Prime`, `Finset.image`, and `Finset.card` in mathlib4.

## What is NOT formalized

- BES-1 (ES exception set finite): requires formalizing the Y_Z divisor
  enumeration as a Lean function. Tractable but not done here.
- BES-2 (Andrica saturation): infinite quantification, not decidable.
- BES-4..10: empirical conjectures, not theorems.

## Author

Elias Oulad Brahim, ORCID 0009-0009-3302-9532

## License

Apache 2.0 (matching mathlib4 conventions).
