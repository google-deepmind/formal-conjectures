# Verification of the distinct-zero corollary

The witness is `17/20`. Michael Devine's 85.0882% dyadic result already exceeds this witness. The proof here uses Kristian Muri Knausgård's subsequent 85.4225% result, for which a single public certificate includes the Riemann hypothesis and the dyadic estimate. The contribution by @domthedeveloper connects the zero counts, proves the strict comparison with the Montgomery–Taylor constant, and supplies an eventually zero error term that works for every positive height.

## Published inputs

The compact replay reported acceptance by Lean's default kernel and nanoda, with only `propext`, `Classical.choice` and `Quot.sound`. We downloaded its archive and matched the uncompressed reference and solution exports to the following SHA-256 values. [Release and verification instructions](https://github.com/josusanmartin/riemann/releases/tag/compact-rh-854225-v1)

| Export | SHA-256 |
| --- | --- |
| Reference | `ab79018d7607a8eb7fbb3091f3b8591c4965cdcf284516b053c48072f8fc79f0` |
| Solution | `e4c9866f587abbeb141cc631136b3ae88a2bbf53f83aa3eb02752d1d19ab8c95` |

## Checks on the deduction

On November 27, 2026, AXLE's `verify_proof` compared the proof against a separately supplied statement. The conclusion came verbatim from DeepMind's theorem at commit `f606af160664c5a10952e9a957b100a1cd45bbeb`. The two inputs were explicit arguments with the types of the certified RH and dyadic theorems. Both checks returned `okay: true` and an empty list of failed declarations. The axiom report for the deduction lists only the three standard axioms above.

| Lean | Verification request |
| --- | --- |
| 4.33.1 | `9c294248-5044-4cb1-84ca-71a97ce22fe7` |
| 4.35.0 | `cf1d22c4-4201-438f-8d02-0a006ff794da` |

`Result.lean` applies the deduction to the two named theorems. For an end-to-end replay on Linux with the pinned Lean 4.35.0 toolchain and the published compact verification runtime, run `bash Proofs/DistinctZeros/verify.sh /path/to/runtime`. The script compiles the exact archived proof, links the compact RH implementation, audits the final axiom list, and invokes Lean's kernel on the export. The November 27 checks reported above verify the components separately.
