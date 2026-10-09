# AEGIS #606 → Formal Conjectures fork port

This directory is a fork-native port of `Aegis-Omega/AEGIS-OMEGA#606`.

- upstream PR: #606
- upstream base: `cfe368ce2ffa0d196a4319c02b956997edf9f3fa`
- upstream exact head: `589adf0480bd4d7c12c9828027ea6228398377f4`
- fork base: `02da1ad1288b4881ea1f8e575fbe84af7db04364`
- imported upstream changed files: 54
- imported Lean bridge files: 50
- imported upstream workflow snapshots: 3
- imported test files: 1

## Layout

- `Source/` preserves the #606 Lean source body at the exact upstream head, with only the standard Formal Conjectures Apache-2 header prepended for fork CI.
- `UpstreamWorkflows/` preserves the three upstream workflow files as inert source snapshots.
- `Test/` preserves the upstream test surface.
- `Compat/` contains fork-local Lean 4.33.1 / Mathlib 0df444a3 elaboration repairs already exercised by the exact-head replay lane.
- `V13Scratch.lean` is the fork-side restricted-Weil / RH bridge used after the #606 dependency closure compiles.
- `.github/workflows/aegis-pr606-fork-replay-v1.yml` is the fork-native replay.

The replay reconstructs #606 as:

```
AEGIS #580 base @ cfe368ce2ffa0d196a4319c02b956997edf9f3fa
       +
local exact #606 Source/
       +
fork Compat/ overrides
       ↓
full topological Lean closure
       ↓
V13 restricted-Weil bridge + axiom audit
```

No theorem/proof body in `Source/` is silently rewritten: the fork-required license header is the only prefix change. Fork-only elaboration repairs are separated in `Compat/`.
