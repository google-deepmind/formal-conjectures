# Checkpoint 2026-10-05 (updated) — the Krein window ring

All modules in this directory compile with `[propext, Classical.choice, Quot.sound]` in one consistent
tree. The tree is `formal-conjectures` `AEGISOverlay` plus the PR #693 versions of
`WeilFixedLineGammaXSpaceV10`, `WeilFixedLineCompletedGammaV10`, `WeilFixedLineGammaFubiniV10` and
`WeilFixedLineGammaAssemblyV10`. Toolchain: Lean 4.33.1, Mathlib `0df444a`.

| Module | Statement |
|---|---|
| `RHKreinZetaBridgeV2` | `certificate_generic` (any symbol S, given the zero-quadratic identity); `certificate3_zero_quadratic_nonneg` (primes 2, 3, `L ≤ log 4`) |
| `RHKreinZetaBridgeV3` | `zero_quadratic_eq_scertM`: for `2r < log (M+1)`, `Re Σ_ρ Z_ρ = (1/2π)∫ ScertM·Nr`, where `ScertM` has all prime powers `< M+1`; `certificateM_zero_quadratic_nonneg` |
| `RHKreinZetaBridgeV4` | `certificate_raw`; `certificate_slack`: `W(S_M − m) + Ĥ + δ + W·s ≥ 0` ⇒ `m·N(g) ≤ Q(g) + K_s(g)` |
| `RHFeshbachCoreV1` | `inner_orth_le`: `w ⊥ U ⇒ ‖⟪w,x⟫‖ ≤ ‖w‖‖x − P_U x‖` (the trace bound by Cauchy–Schwarz); `feshbach_lower`: the scalar Schur step |
| `RHExactLDLTV1` | `ldltCheck_sound`: a rational `A = L D Lᵀ` with `D ≥ 0`, checked by a `Bool` and `decide +kernel`, gives `0 ≤ Re Σ z̄ᵢ zⱼ Aᵢⱼ` for every complex `z` |
| `RHPlancherelPacketV1` | `energy_eq_L2`: `(1/2π)∫ Nr g = ∫ ‖Gm g u‖²` (Plancherel for packets) |
| `RHMollifyV1` | `fourier_moll_sub_one`: normalized smooth bump on `(−ε, ε)`, `‖𝓕ρ_ε(ξ) − 1‖ ≤ (2πεξ)²/2` |

## How the ring closes (plan; `✓` = in Lean)

1. ✓ Bridge for any window (V3) and the complement inequality `Q ≥ m·N − K` (V4).
2. ✓ Moment-zero vanishing and the Krein pairing: `RHKreinFactorV13`, `RHKreinPairingV13`,
   `RHKreinDeltaPairingV1`.
3. ✓ `Q` is sesquilinear on packets: `WeilMixedAlgebraV2`, `RHGramExpansionV13.B_packetSum`.
4. ✓ The Cauchy–Schwarz slack bound and the Schur step (`RHFeshbachCoreV1`).
5. ✓ The low block can stay in the `C^∞` class. Columns are mollified splines `φ = spline ⋆ ρ_ε`
   with `φ̂ = ŝpline · ρ̂_ε` and `|ρ̂_ε − 1| ≤ (2πεξ)²/2` (`RHMollifyV1`).
6. ◐ The concrete assembly. ✓ Plancherel identification `N(g) = ‖G‖²` (`RHPlancherelPacketV1`).
   ✓ Exact rational LDLᵀ for the Schur matrix (`RHExactLDLTV1`). ☐ `ŵ(t) = ⟨w, e_t⟩`, the low-block
   entries `B(φ_i, φ_j)` and the cross bound `β(v)` with the Taylor-model checker.
7. ☐ Kernel runs of the Arb Krein + slack certificates (L = 1.05 … 1.8, `feshbach_arb_v1/v2` in
   AEGIS-OMEGA). They need `checkWide` extended by the step-function slack.

## Kernel runs at this checkpoint

- **L = 4/5** (`../krein_reflective_v1`): all 219 batches OK. `RHKreinAllCellsV1` compiles with the standard axioms.
- **L = 21/20** (`../krein_L105_v1`): kernel run complete (133 batch modules). `RHWindowL105FinalV1`
  compiles with the standard axioms: every window `L < 21/40` has the arithmetic sign, and RH
  follows from the sign on the windows `L ≥ 21/40`.
  - `tools/design105F.json` (209 KB) is not committed. Regenerate it with
    `python3 sweep.py && python3 minN.py && python3 deg16.py`; these are exact Fraction
    computations and deterministic.

Not RH. Every result is for a fixed support width. AUTHORITY_EFFECT = NONE.
