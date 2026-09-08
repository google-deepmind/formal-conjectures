# Development Plan: the lattice and integral real periods of an elliptic curve over ℝ agree

Repository `formal-conjectures`, branch `periods`. Planned 2026-09-08. Lean v4.33.1 / Mathlib v4.33.1.

## Goal

```lean
theorem WeierstrassCurve.leastRealPeriodIntegral_eq_leastRealPeriod
    (W : WeierstrassCurve ℝ) [W.IsElliptic] : W.leastRealPeriodIntegral = W.leastRealPeriod

theorem WeierstrassCurve.realPeriodIntegral_eq_realPeriod
    (W : WeierstrassCurve ℝ) [W.IsElliptic] : W.realPeriodIntegral = W.realPeriod
```

`leastRealPeriodIntegral = 2 ∫_{e₁}^∞ dx/√(4x³ + b₂x² + 2b₄x + b₆)` (file `PeriodIntegral.lean`) and
`leastRealPeriod` = least positive real element of the period lattice with `g₂ = c₄/12`, `g₃ = c₆/216`
(file `RealPeriod.lean`). Both are then multiplied by `nrRealComponents` to give the real period of BSD.

## References (how each maps to the plan)

| Reference | Used for |
|-----------|----------|
| DLMF §23.2–23.3 (https://dlmf.nist.gov/23.3) | definitions; `e_j = ℘(ω_j)`; `℘'² = 4℘³ − g₂℘ − g₃` (23.3.10/11) |
| DLMF §23.5 (https://dlmf.nist.gov/23.5) | ℘ real on ℝ iff lattice real (23.5(i)); rectangular/rhombic cases |
| DLMF §23.6(iv) (https://dlmf.nist.gov/23.6) | the statement: `2ω₁ = ∫_{e₁}^∞ du/√(…)` (23.6.34), general (23.6.36) |
| Pastras, arXiv:1706.07371, §1, §3.1, App. A | the proof: inversion of the integral by `x = ℘(t)`, zeros of `℘'`, monotonicity on the real axis, minimality of the real half-period |
| Cremona, *Algorithms*, §3.7 pp. 97–98 | the two cases Δ > 0 / Δ < 0 and "ω₁ a positive real period" |
| Silverman AEC VI Prop 3.6(a) | classical proof of "zeros of ℘' are half-periods" (order count — the API gap) |

Local extractions of Pastras and Cremona are in the session's tool-results directory (`fourlectures.txt`,
`cremona3.txt`).

## What already exists (checked 2026-09-08)

- **LeanBridge** (`LeanBridge/LeanBridge/{NonSlop,work,SayebWork}`): uniformisation map `ℂ/Λ → E(ℂ)`
  (`NonSlop/uniformisation.lean`), addition theorem (`work/addition_euler.lean`, 1213 lines, described by
  the user as slop), injectivity/surjectivity skeleton (`work/inverse.lean`, one sorry
  `exists_weierstrassP_eq`), lattice existence (`work/backward.lean`), scaling/conjugation and the
  uniqueness theorem (`SayebWork/`). **Nothing there treats the real axis, real periods, or the integral.**
  The pieces relevant to this project (Eisenstein bridge, j-surjectivity, existence, uniqueness, conjugation)
  were already ported to `FormalConjecturesTest/RealPeriod/*.lean` (sorry-free). The complex-analytic
  uniformisation (addition theorem, group isomorphism) is **not needed** for the period equivalence and is
  not imported; the only fact from that circle of ideas we need — zeros of `℘'` are half-periods — is proved
  directly from the ODE (see decomposition.md).
- **Mathlib** `Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`: `℘`, `℘'`, evenness, periodicity,
  analyticity off the lattice, meromorphy and `order_weierstrassP = -2`, `derivWeierstrassP_sq`
  (`℘'² = 4℘³ − g₂℘ − g₃`), `deriv_weierstrassP`, Laurent germs `℘[L - l₀]`.
- **Project** `PeriodIntegral.lean` (integral side, sorry-free), `RealPeriod.lean` (lattice side, sorry-free),
  `RealPeriod/Uniqueness.lean` (has `eventually_deriv_derivWeierstrassP : ℘'' = 6℘² − g₂/2` near `0`, the
  Laurent expansion, and the order-comparison pattern `lattice_le_of_eqOn`).

## Mathlib inventory

| Concept | Mathlib status | Our action |
|---------|----------------|------------|
| ℘, ℘', differential equation, periodicity, evenness, analyticity, order at poles | `PeriodPair.*` in Weierstrass.lean | USE |
| ℘'' = 6℘² − g₂/2 | absent (project has it near 0) | PROVE on ℂ∖Λ (`deriv_derivWeierstrassP`) |
| zeros of ℘' are half-periods | absent | PROVE (`derivWeierstrassP_eq_zero_iff`) via ODE uniqueness |
| local uniqueness of ODE solutions | `ODE_solution_unique_of_eventually` | USE |
| locally Lipschitz from C¹ | `ContDiffAt.exists_lipschitzOnWith` | USE |
| identity theorem | `AnalyticOnNhd.eqOn_of_preconnected_of_{eventuallyEq,frequently_eq}` | USE |
| complement of countable set connected | `Set.Countable.isConnected_compl_of_one_lt_rank` | USE (wrap for ℂ) |
| conj of a tsum | `Complex.conj_tsum` | USE |
| real derivative of a complex function | `HasDerivAt.real_of_complex`, `HasDerivAt.comp_ofReal` | USE |
| strict monotonicity from sign of derivative | `strictAntiOn_of_deriv_neg` | USE |
| intermediate value | `intermediate_value_Ioo`, `intermediate_value_Ioo'` | USE |
| one-dimensional change of variables | `MeasureTheory.integral_image_eq_integral_abs_deriv_smul` | USE |
| ℘ real-valued on ℝ for real lattices | absent | PROVE (`IsReal.coe_weierstrassPRe`) |
| the elliptic integral equals Ω/2 | absent | PROVE (`IsReal.integral_inv_sqrt_eq_half`) |

Rule applied: nothing redefined. The two new `def`s (`weierstrassPRe`, `derivWeierstrassPRe`, the real parts
of ℘, ℘' on ℝ) carry API: coercion lemmas, derivative, continuity, differential equation, limits at the pole,
monotonicity, image.

## File structure

- `FormalConjecturesTest/RealPeriod/HalfPeriods.lean` — general lattices: `℘'' = 6℘² − g₂/2`,
  `derivWeierstrassP_eq_zero_iff`. Imports specific Mathlib files + `RealPeriod/Uniqueness.lean`.
- `FormalConjecturesTest/RealPeriod/RealAxis.lean` — real lattices: conjugation of ℘, the real functions,
  monotonicity on `(0, Ω/2]`, the largest root, the elliptic integral. Imports `Conjugation.lean`,
  `HalfPeriods.lean`, specific Mathlib files. The least positive real period enters only through a
  hypothesis `hΩ : IsLeast {x : ℝ | (x : ℂ) ∈ L.lattice ∧ 0 < x} Ω`, so the file does not depend on the
  choice function in `RealPeriod.lean` (which imports all of Mathlib and is slow to build).
- `FormalConjecturesTest/RealPeriodIntegral.lean` — the `WeierstrassCurve` statements. Imports
  `PeriodIntegral.lean`, `RealPeriod.lean`, `RealAxis.lean`.

Existing files are not modified (the sentence "That the two versions agree is the uniformisation theorem,
which is not proved here" in `PeriodIntegral.lean`'s docstring may be updated at CLEANUP-6 to point to the
new file; user's call).

## Dependency graph

```
Mathlib ℘ API ──┬─▶ H1 H2 H3 H4 ─┐
Uniqueness.lean ┴─▶ H5 ─▶ H6 ────┼─▶ H8 (ODE) ─▶ H9 (identity thm) ─▶ H10 ─▶ H11 derivWeierstrassP_eq_zero_iff
                        H7 ──────┘                                                   │
Conjugation.lean ─▶ R1 R2 ─▶ R3 R4 ─▶ R6 R7 ─┐                                       │
                                   R8 R9 ────┼─▶ R10 ─────────────────────┐          │
                                   R11 R12 ──┤                            │          │
                       R13 ─▶ R14 ───────────┤    R15 ◀───────────────────┼──────────┘
                                             ├─▶ R16 ─▶ R17 ─▶ R18 ─▶ R20 ─┤
                                             │                  R19 ◀─────┤
                                             └─▶ R21b ─▶ R21 ◀────────────┘
PeriodIntegral.lean ─┐
RealPeriod.lean ─────┼─▶ F1 F2 ─▶ F1' F2' ─▶ F3 (e₁ + b₂/12 = ℘(Ω/2)) ─▶ R1 (milestone) ─▶ R2
RealAxis.lean ───────┘
```

## Generality decisions

- Everything at the `PeriodPair` level is stated for an arbitrary `L : PeriodPair`; realness is the
  hypothesis `hL : L.IsReal` (conjugation-stable lattice), never "g₂, g₃ real" (that is `isReal_iff_exists_real`).
- The least positive real period is a hypothesis `hΩ : IsLeast {x : ℝ | (x : ℂ) ∈ L.lattice ∧ 0 < x} Ω`, not
  `L.leastRealPeriod hL`, so the lemmas are usable for any witness and do not depend on `Classical.choose`.
- `derivWeierstrassP_eq_zero_iff` and `deriv_derivWeierstrassP` hold for every lattice, not just real ones.
- The cubic is written with `L.g₂.re`, `L.g₃.re` so that no extra `a b : ℝ` variables are threaded through;
  for a real lattice these are `g₂`, `g₃`.
- No case split on the sign of Δ (rectangular vs rhombic): the least positive real period makes the statement
  uniform. This is more general than DLMF 23.6.34 (rectangular) and matches 23.6.36 (any lattice).
- `WeierstrassCurve` results assume only `[W.IsElliptic]`, as the two definitions do.

## Cleanup cadence
16 proof tickets → 6 per-file cleanups (`CLEANUP-1..6`), one `CLEANUP-ALL-1` before the milestone `T016`,
and `CLEANUP-FINAL`. See `tickets.md`.

## ChatGPT validation
The `chatgpt-math` MCP server failed to connect this session; the plan-validation step was skipped.
