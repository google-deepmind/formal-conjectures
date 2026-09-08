# Ticket Board: lattice real period = integral real period

Project root: `/Users/nkw24xru/Desktop/Lean/formal-conjectures` (branch `periods`).
Plan: `.mathlib-quality/plan.md`. Decomposition (source quotes, attacks, verified names):
`.mathlib-quality/decomposition.md`. Build rule: build only the touched module, e.g.
`lake build FormalConjecturesTest.RealPeriod.HalfPeriods` (never the whole library). The test library has
`warn.sorry = false`, so check for remaining sorries with `grep -n sorry <file>`.

Notation: inside `namespace PeriodPair`, `℘[L]` = `weierstrassP L`, `℘'[L]` = `derivWeierstrassP L`,
`℘[L - l₀]` = `weierstrassPExcept L l₀`, `℘'[L - l₀]` = `derivWeierstrassPExcept L l₀` (scoped notation
from Mathlib's `Weierstrass.lean`). `Λ` below means `L.lattice`.

## Summary
- Total: 24 tickets (16 proof/definition, 8 cleanup)
- Open: 0 | In Progress: 0 | Done: 24 (board complete 2026-09-08T19:14Z)
- Parallel capacity: 3 (T001/T006/T014 can start at once; T003 ∥ T007/T008; T009 ∥ T010 chain)

Dependency order: T001 → T002 → T003 → CLEANUP-1 → T004 → T005 → CLEANUP-2;
T006 → T007 → T008 → CLEANUP-3 → T009 → T010 → T011 → CLEANUP-4 → T012 → T013 → CLEANUP-5;
T014 → T015 → CLEANUP-ALL-1 → T016 → CLEANUP-6 → CLEANUP-FINAL.
(T009 needs T005; T012 needs T011; T015 needs T013 and T014; T016 needs T015.)

---

## Tickets

### [T001] Basic lemmas of HalfPeriods.lean
- **Status**: done (finished 2026-09-08T16:40Z)
- **Progress**:
  - 2026-09-08T16:40: DONE — all six lemmas proved. `isPreconnected_compl_of_countable` is one term
    (`isConnected_compl_of_one_lt_rank` + `rank_real_complex`); the two congr lemmas are `unfold; rw [h]`;
    `countable_lattice` is `countable_of_Lindelof_of_discrete` directly (no `countable_coe_iff` needed — the
    coercion elaborates); `hasDerivAt_weierstrassP` is `simpa using …differentiableAt.hasDerivAt`;
    `derivWeierstrassP_eq_zero_of_two_mul_mem` needed `h1.symm` (orientation) into `CharZero.eq_neg_self_iff`.
    `lake build` clean; `#print axioms` on all six shows only propext/Classical.choice/Quot.sound.
- **File**: FormalConjecturesTest/RealPeriod/HalfPeriods.lean
- **Depends on**: none
- **Parallel**: yes
- **Type**: lemmas (6 sorries: lines 62, 73, 77, 82, 88, 107)

#### Statement
```lean
lemma Complex.isPreconnected_compl_of_countable {s : Set ℂ} (hs : s.Countable) :
    IsPreconnected sᶜ := by sorry

lemma weierstrassP_congr {L₁ L₂ : PeriodPair} (h : L₁.lattice = L₂.lattice) : ℘[L₁] = ℘[L₂] := by sorry

lemma derivWeierstrassP_congr {L₁ L₂ : PeriodPair} (h : L₁.lattice = L₂.lattice) :
    ℘'[L₁] = ℘'[L₂] := by sorry

lemma countable_lattice : (L.lattice : Set ℂ).Countable := by sorry

lemma hasDerivAt_weierstrassP {z : ℂ} (hz : z ∉ L.lattice) : HasDerivAt ℘[L] (℘'[L] z) z := by sorry

lemma derivWeierstrassP_eq_zero_of_two_mul_mem {z : ℂ} (h : 2 * z ∈ L.lattice) : ℘'[L] z = 0 := by sorry
```

#### Proof sketch
1. `isPreconnected_compl_of_countable`: `(hs.isConnected_compl_of_one_lt_rank (by rw [Complex.rank_real_complex]; exact one_lt_two)).isPreconnected`.
   (`Set.Countable.isConnected_compl_of_one_lt_rank (h : 1 < Module.rank ℝ E) (hs : s.Countable) : IsConnected sᶜ`.)
2. `weierstrassP_congr`: `funext z; unfold weierstrassP; rw [h]` — copy of `G_congr` in `Conjugation.lean:82`.
   Same for `derivWeierstrassP_congr` with `derivWeierstrassP`.
3. `countable_lattice`: `Set.countable_coe_iff.mp (countable_of_Lindelof_of_discrete (X := L.lattice))` — the
   instance `DiscreteTopology L.lattice` is in Mathlib; Lindelöf comes from second countability of ℂ. This is the
   `hΛ` line of `exists_isLeast_pos_real` in `RealPeriod.lean`; if `countable_coe_iff` direction fights, use
   `Set.countable_coe_iff` / `Set.Countable.of_subtype` variants.
4. `hasDerivAt_weierstrassP`: `have := (L.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt;
   rwa [deriv_weierstrassP] at this` (Uniqueness.lean line ~105 does `simpa using hd.hasDerivAt`).
5. `derivWeierstrassP_eq_zero_of_two_mul_mem`: `have h1 := L.derivWeierstrassP_sub_coe z ⟨2 * z, h⟩` gives
   `℘'[L] (z - 2 * z) = ℘'[L] z`; `rw [show z - 2 * z = -z by ring, derivWeierstrassP_neg] at h1`; conclude by
   `CharZero.eq_neg_self_iff.mp h1.symm` (or `linear_combination h1 / 2` after `neg_eq_iff`).

#### Mathlib lemmas needed
`Set.Countable.isConnected_compl_of_one_lt_rank`, `Complex.rank_real_complex`, `IsConnected.isPreconnected`,
`countable_of_Lindelof_of_discrete`, `Set.countable_coe_iff`, `PeriodPair.analyticOnNhd_weierstrassP`,
`AnalyticAt.differentiableAt`, `DifferentiableAt.hasDerivAt`, `PeriodPair.deriv_weierstrassP`,
`PeriodPair.derivWeierstrassP_sub_coe`, `PeriodPair.derivWeierstrassP_neg`, `CharZero.eq_neg_self_iff`.

#### Sources
DLMF 23.2.4 (℘ as a lattice sum); Pastras (1.35) for the half-period computation (decomposition H0–H4, H7).

#### Generality decision
All for arbitrary `L : PeriodPair`; `derivWeierstrassP_eq_zero_of_two_mul_mem` has no `z ∉ Λ` hypothesis
(true on Λ by the junk convention).

---

### [T002] The second-order differential equation
- **Status**: done (finished 2026-09-08T16:52Z)
- **Progress**:
  - 2026-09-08T16:52: DONE. Identity theorem as planned. Two deviations from the sketch, both minor:
    the analyticity of `6℘² - g₂/2` is `intro w hw; have := analyticOnNhd_weierstrassP w hw; fun_prop`;
    the witness `z₀ ≠ 0` in `V` comes from `Filter.nonempty_of_mem (Filter.inter_mem hmem
    self_mem_nhdsWithin)` on `𝓝[≠] 0` (the `𝓝[V] 0` route needs a `NeBot` instance that is not
    available). `hasDerivAt_derivWeierstrassP` is `rw [← deriv_derivWeierstrassP hz]` then
    `differentiableAt.hasDerivAt`. Axioms clean.
- **File**: FormalConjecturesTest/RealPeriod/HalfPeriods.lean
- **Depends on**: T001
- **Parallel**: yes (with T006–T008, T014)
- **Type**: lemmas (2 sorries: lines 94, 99)

#### Statement
```lean
lemma deriv_derivWeierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    deriv ℘'[L] z = 6 * ℘[L] z ^ 2 - L.g₂ / 2 := by sorry

lemma hasDerivAt_derivWeierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt ℘'[L] (6 * ℘[L] z ^ 2 - L.g₂ / 2) z := by sorry
```

#### Proof sketch
1. Set `f := deriv ℘'[L]`, `g := fun w ↦ 6 * ℘[L] w ^ 2 - L.g₂ / 2`, `U := (L.lattice : Set ℂ)ᶜ`.
2. `hf : AnalyticOnNhd ℂ f U := L.analyticOnNhd_derivWeierstrassP.deriv`;
   `hg : AnalyticOnNhd ℂ g U := ((L.analyticOnNhd_weierstrassP.pow 2).const_mul 6).sub analyticOnNhd_const`
   (or `fun z hz ↦ by have := L.analyticOnNhd_weierstrassP z hz; fun_prop`).
3. `hU : IsPreconnected U := Complex.isPreconnected_compl_of_countable L.countable_lattice`.
4. From `L.eventually_notMem_lattice.and L.eventually_deriv_derivWeierstrassP : ∀ᶠ w in 𝓝[≠] 0, w ∉ Λ ∧ f w = g w`
   extract an open set: `obtain ⟨V, hV0, hVo, hV⟩ := eventually_nhdsWithin_iff.mp this |> eventually_nhds_iff.mp`
   giving `∀ w ∈ V, w ≠ 0 → (w ∉ Λ ∧ f w = g w)`, `V` open, `0 ∈ V`.
5. Pick `z₀ ∈ V`, `z₀ ≠ 0` (e.g. `(hVo.mem_nhds hV0)` is in `𝓝 0`, so `V \ {0} ∈ 𝓝[≠] 0`, nonempty by
   `Filter.nonempty_of_mem`). Then `hz₀ : z₀ ∈ U` and
   `hfg : f =ᶠ[𝓝 z₀] g` from `(hVo.sdiff isClosed_singleton).mem_nhds ⟨hz₀V, hz₀ne⟩` and `hV`.
6. `exact hf.eqOn_of_preconnected_of_eventuallyEq hg hU hz₀ hfg hz`.
7. `hasDerivAt_derivWeierstrassP`: `(L.analyticOnNhd_derivWeierstrassP z hz).differentiableAt.hasDerivAt` then
   `rw [L.deriv_derivWeierstrassP hz] at this`.

Bridging: if `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` wants `(hf) (hg) (hU) (h₀) (hfg) : EqOn f g U`,
apply the result at `z` with `hz`.

#### Mathlib lemmas needed
`PeriodPair.eventually_deriv_derivWeierstrassP` (project, Uniqueness.lean:97),
`PeriodPair.eventually_notMem_lattice` (Uniqueness.lean:53), `AnalyticOnNhd.deriv`,
`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` (Analytic/Uniqueness.lean:223), `eventually_nhdsWithin_iff`
(NhdsWithin.lean:49), `eventually_nhds_iff`, `IsOpen.sdiff`, `IsOpen.mem_nhds`, `PeriodPair.analyticOnNhd_derivWeierstrassP`,
`PeriodPair.analyticOnNhd_weierstrassP`, `AnalyticOnNhd.pow`, `AnalyticOnNhd.const_mul`/`mul`, `AnalyticOnNhd.sub`,
`analyticOnNhd_const`.

#### Sources
DLMF 23.3.10 differentiated; project Uniqueness.lean docstring step 2 (decomposition H5, H6).

#### Generality decision
Any lattice, any `z ∉ Λ`. The identity is stated with `deriv` so that `hasDerivAt_derivWeierstrassP` is a corollary.

---

### [T003] Local symmetry at a zero of ℘' (ODE uniqueness)
- **Status**: done (finished 2026-09-08T17:05Z)
- **Progress**:
  - 2026-09-08T17:05: DONE, sketch followed exactly. Bridging needed beyond the sketch:
    `ContinuousAt.tendsto` for the two `Tendsto (fun t ↦ z₀ ± ↑t)` facts (`simpa using h.tendsto`);
    `Pi.neg_def` + `neg_neg` to turn `HasDerivAt (-f)` into `HasDerivAt (fun t ↦ -f t)` with the
    double negation cancelled. `hf0.trans hg0.symm` supplies `heq`. Axioms clean.
- **File**: FormalConjecturesTest/RealPeriod/HalfPeriods.lean
- **Depends on**: T002
- **Parallel**: yes (with T006–T008)
- **Type**: lemma (1 sorry: line 113)

#### Statement
```lean
lemma eventually_weierstrassP_add_eq_sub {z₀ : ℂ} (hz₀ : z₀ ∉ L.lattice) (h : ℘'[L] z₀ = 0) :
    ∀ᶠ t : ℝ in 𝓝 0, ℘[L] (z₀ + t) = ℘[L] (z₀ - t) := by sorry
```

#### Proof sketch
1. Vector field `v : ℝ → ℂ × ℂ → ℂ × ℂ := fun _ p ↦ (p.2, 6 * p.1 ^ 2 - L.g₂ / 2)`. It is `ContDiff ℂ 1`
   (`contDiff_snd.prodMk (((contDiff_fst.pow 2).const_mul _).sub contDiff_const)` or `by fun_prop`), so
   `obtain ⟨K, S, hS, hK⟩ := (hv.contDiffAt (x := (℘[L] z₀, 0))).exists_lipschitzOnWith` — `S ∈ 𝓝 (℘[L] z₀, 0)`,
   `LipschitzOnWith K (v 0) S`. Use `s := fun _ ↦ S`.
2. `f : ℝ → ℂ × ℂ := fun t ↦ (℘[L] (z₀ + t), ℘'[L] (z₀ + t))`,
   `g : ℝ → ℂ × ℂ := fun t ↦ (℘[L] (z₀ - t), -℘'[L] (z₀ - t))`.
3. `hne : ∀ᶠ t : ℝ in 𝓝 0, z₀ + t ∉ Λ ∧ z₀ - t ∉ Λ`: `Λᶜ` is open (`L.isClosed_lattice.isOpen_compl`) and
   `t ↦ z₀ ± ↑t` is continuous with value `z₀` at `0` (`Complex.continuous_ofReal`); use
   `(hopen.mem_nhds hz₀)` pulled back by `ContinuousAt.tendsto` / `Filter.Tendsto.eventually`.
4. Derivatives, for `t` with `z₀ + t ∉ Λ`:
   `HasDerivAt (fun t : ℝ ↦ ℘[L] (z₀ + t)) (℘'[L] (z₀ + t)) t` :=
   `((L.hasDerivAt_weierstrassP h1).comp_const_add z₀ (t : ℂ)).comp_ofReal` (statement shape
   `HasDerivAt (fun y : ℝ ↦ (fun w ↦ ℘[L] (z₀ + w)) ↑y) _ t`, definitionally the goal);
   `HasDerivAt (fun t : ℝ ↦ ℘'[L] (z₀ + t)) (6 * ℘[L] (z₀ + t) ^ 2 - L.g₂ / 2) t` similarly from
   `hasDerivAt_derivWeierstrassP`; combine with `HasDerivAt.prodMk`. Check `v t (f t)` reduces to the pair
   `(℘'[L] (z₀+t), 6 * ℘[L] (z₀+t) ^ 2 - L.g₂/2)` by `rfl`/`show`.
   For `g`: `HasDerivAt.comp_const_sub z₀ (t : ℂ)` gives derivative `-(℘'[L] (z₀ - t))` for the first
   component and `-(6 * ℘[L] (z₀ - t) ^ 2 - L.g₂ / 2)` for `℘'[L] (z₀ - ·)`, so `HasDerivAt.neg` gives
   `6 * ℘[L] (z₀ - t) ^ 2 - L.g₂ / 2` for the second component: again `v t (g t)` by `rfl` (`neg_neg`).
5. Membership: `f`, `g` are continuous at `0` (from the `HasDerivAt`s, `HasDerivAt.continuousAt`) with
   `f 0 = (℘[L] z₀, ℘'[L] z₀) = (℘[L] z₀, 0)` (`Complex.ofReal_zero, add_zero, h`) and
   `g 0 = (℘[L] z₀, -℘'[L] z₀) = (℘[L] z₀, 0)` (`sub_zero, h, neg_zero`); so `∀ᶠ t, f t ∈ S` by
   `(hf0.continuousAt).eventually_mem hS` (rewrite the value first), same for `g`.
6. `heq : f 0 = g 0` by `simp [f, g, h]`.
7. `have := ODE_solution_unique_of_eventually (v := v) (s := fun _ ↦ S) (K := K) (t₀ := 0)
   (Eventually.of_forall fun _ ↦ hK) hf hg heq : f =ᶠ[𝓝 0] g`; then `filter_upwards [this] with t ht` and
   `exact congrArg Prod.fst ht`.

Bridging tactics: `Prod.ext_iff`, `Prod.mk.injEq`, `show` to unfold `v`/`f`/`g`; `push_cast` for `((t:ℝ):ℂ)`.

#### Mathlib lemmas needed
`ODE_solution_unique_of_eventually` (Analysis/ODE/ExistUnique.lean:312), `ContDiffAt.exists_lipschitzOnWith`
(ContDiff/RCLike.lean:131), `ContDiff.contDiffAt`, `contDiff_fst`, `contDiff_snd`, `ContDiff.prodMk`, `ContDiff.pow`,
`ContDiff.sub`, `contDiff_const`, `HasDerivAt.comp_const_add` (Deriv/Shift.lean:27), `HasDerivAt.comp_const_sub`
(Deriv/Shift.lean:37), `HasDerivAt.comp_ofReal` (Complex/RealDeriv.lean:97), `HasDerivAt.prodMk` (Deriv/Prod.lean:51),
`HasDerivAt.neg`, `HasDerivAt.continuousAt`, `ContinuousAt.eventually_mem`, `PeriodPair.isClosed_lattice`,
`Complex.continuous_ofReal`, `Filter.Eventually.of_forall`, plus T001/T002 lemmas.

#### Sources
Pastras p. 12 "general solution … y = ℘(z + z₀)" (decomposition H8; this is the API-gap resolution — the source's
"order 3" count is replaced by ODE uniqueness).

#### Generality decision
Arbitrary lattice and arbitrary `z₀ ∉ Λ`; the real line through `z₀` in direction `1` suffices for T004.

---

### [CLEANUP-1] Run /cleanup on HalfPeriods.lean
- **Status**: done (finished 2026-09-08T17:20Z)
- **Progress**:
  - 2026-09-08T17:20: /cleanup run on the T001-T003 declarations. Baseline clean. Fixed: two lines
    over 100 chars (docstring reference and the final `⟨_, _⟩` term). Golfed: `obtain`+`exact ⟨…⟩`
    collapsed to a direct `obtain` of the `Nonempty`; two `have := …; exact this` wrappers became
    term-mode with `hf0 ▸ hS`; `rw … at hd; exact hd` → `rwa`; unused `with hv` binding dropped;
    anonymous `have :=` given names. 202 → 199 lines. `simp only [weierstrassP, h]` does NOT work
    in place of `unfold weierstrassP; rw [h]` (simp cannot unfold the def) — reverted. Style scan
    clean: max width 100, no λ/$-operator/push_neg/set_option/haveI/letI/erw/FIXME, no subsection
    dividers, private-vs-docstring rule satisfied (all decls public with one-sentence docstrings).
    Axioms clean; downstream RealAxis still builds.
- **File**: FormalConjecturesTest/RealPeriod/HalfPeriods.lean
- **Depends on**: T003
- **Parallel**: no
- **Type**: cleanup
- **Description**: `/cleanup` on the file after 3 proof tickets (cadence rule). Golf T001–T003, check docstrings, imports (drop unused), naming.

---

### [T004] Global symmetry at a zero of ℘' (identity theorem)
- **Status**: done (finished 2026-09-08T17:30Z)
- **Progress**:
  - 2026-09-08T17:30: DONE. `U` proved equal to the complement of the two shifted lattice images by
    an explicit `ext`/`constructor` (the `simp [sub_eq_iff_eq_add]` route from the sketch did not
    close it); preconnectedness then from T001. Analyticity of both sides by `AnalyticOnNhd.comp`
    with `by fun_prop` for the affine inner maps. `0 ∈ U` needs `add_zero`/`sub_zero` first.
- **File**: FormalConjecturesTest/RealPeriod/HalfPeriods.lean
- **Depends on**: CLEANUP-1
- **Parallel**: yes (with T006–T011)
- **Type**: lemma (1 sorry: line 120)

#### Statement
```lean
lemma weierstrassP_add_eq_sub_of_derivWeierstrassP_eq_zero {z₀ : ℂ} (hz₀ : z₀ ∉ L.lattice)
    (h : ℘'[L] z₀ = 0) {z : ℂ} (hz : z₀ + z ∉ L.lattice) (hz' : z₀ - z ∉ L.lattice) :
    ℘[L] (z₀ + z) = ℘[L] (z₀ - z) := by sorry
```

#### Proof sketch
1. `U : Set ℂ := {w | z₀ + w ∉ Λ ∧ z₀ - w ∉ Λ}`. Show `U = ((fun l ↦ l - z₀) '' Λ ∪ (fun l ↦ z₀ - l) '' Λ)ᶜ`
   (`ext w; simp [sub_eq_iff_eq_add, eq_sub_iff_add_eq]`, or prove `IsPreconnected U` via
   `Complex.isPreconnected_compl_of_countable` applied to that countable set and `convert`). Countability:
   `(L.countable_lattice.image _).union (L.countable_lattice.image _)`.
2. `F := fun w ↦ ℘[L] (z₀ + w)`, `G := fun w ↦ ℘[L] (z₀ - w)`. Analytic on `U`:
   `L.analyticOnNhd_weierstrassP.comp (analyticOnNhd_const.add analyticOnNhd_id) (fun w hw ↦ hw.1)` — check
   `AnalyticOnNhd.comp {s t} (hg : AnalyticOnNhd 𝕜 g t) (hf : AnalyticOnNhd 𝕜 f s) (st : MapsTo f s t)`
   (Composition.lean:892); similarly `G` with `analyticOnNhd_const.sub analyticOnNhd_id` and `hw.2`.
3. `h0 : (0 : ℂ) ∈ U := ⟨by simpa using hz₀, by simpa using hz₀⟩`.
4. Frequently: `hev := L.eventually_weierstrassP_add_eq_sub hz₀ h : ∀ᶠ t : ℝ in 𝓝 0, F ↑t = G ↑t`.
   `hfreq : ∃ᶠ t : ℝ in 𝓝[≠] 0, F ↑t = G ↑t := (hev.filter_mono nhdsWithin_le_nhds).frequently`.
   `hT : Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] 0) (𝓝[≠] 0) := tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
   (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
   (eventually_mem_nhdsWithin.mono fun t ht ↦ by simpa using ht)` (uses `Complex.ofReal_ne_zero`; `Complex.ofReal_zero`).
   `hfg : ∃ᶠ w in 𝓝[≠] (0:ℂ), F w = G w := hT.frequently hfreq`.
5. `exact hF.eqOn_of_preconnected_of_frequently_eq hG hU h0 hfg ⟨hz, hz'⟩`.

#### Mathlib lemmas needed
`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` (Analytic/IsolatedZeros.lean:238), `AnalyticOnNhd.comp`
(Composition.lean:892), `analyticOnNhd_const`, `analyticOnNhd_id`, `AnalyticOnNhd.add/sub`, `Set.Countable.image`,
`Set.Countable.union`, `Filter.Eventually.frequently`, `Filter.Eventually.filter_mono`, `nhdsWithin_le_nhds`,
`Filter.Tendsto.frequently` (Order/Filter/Tendsto.lean:55), `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within`
(NhdsWithin.lean:460), `eventually_mem_nhdsWithin`, `Complex.ofReal_ne_zero`, `Complex.continuous_ofReal`, T001, T003.

#### Sources
Identity theorem, as in project `Uniqueness.lean` step 3 (decomposition H9).

#### Generality decision
Stated for all `z` with both points off the lattice (junk values otherwise).

---

### [T005] Zeros of ℘' are half-periods
- **Status**: done (finished 2026-09-08T17:38Z)
- **Progress**:
  - 2026-09-08T17:38: DONE — HalfPeriods.lean is now sorry-free and `derivWeierstrassP_eq_zero_iff`
    is proved. Order-comparison as sketched (`meromorphicOrderAt_congr` + `order_weierstrassP` +
    `AnalyticAt.meromorphicOrderAt_nonneg`, contradiction by `decide`). The neighbourhood
    `{w | 2z₀ - w ∉ Λ}` must come from `ContinuousAt.preimage_mem_nhds` with `exact`, not `simpa`
    (simp normalises the preimage into a different but defeq presentation and then fails to match).
- **File**: FormalConjecturesTest/RealPeriod/HalfPeriods.lean
- **Depends on**: T004
- **Parallel**: yes (with T006–T008)
- **Type**: lemma (1 sorry: line 128; `derivWeierstrassP_eq_zero_iff` at line 134 is already proved from it)

#### Statement
```lean
lemma two_mul_mem_lattice_of_derivWeierstrassP_eq_zero {z₀ : ℂ} (hz₀ : z₀ ∉ L.lattice)
    (h : ℘'[L] z₀ = 0) : 2 * z₀ ∈ L.lattice := by sorry
```

#### Proof sketch (mirror `lattice_le_of_eqOn`, Uniqueness.lean:318–340)
1. `by_contra h2`.
2. `hev : ℘[L] =ᶠ[𝓝[≠] (0:ℂ)] fun w ↦ ℘[L] (2 * z₀ - w)`: `filter_upwards [L.eventually_notMem_lattice,
   mem_nhdsWithin_of_mem_nhds ((L.isClosed_lattice.isOpen_compl.mem_nhds h2).preimage? …)]` — concretely, the set
   `{w | 2 * z₀ - w ∉ Λ}` is a neighbourhood of `0` because `w ↦ 2 * z₀ - w` is continuous and `2 * z₀ ∈ Λᶜ` open:
   `((continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds (by simpa using
   L.isClosed_lattice.isOpen_compl.mem_nhds h2))`. For such `w`: apply T004 with `z := w - z₀`:
   `hz : z₀ + (w - z₀) ∉ Λ` (`add_sub_cancel`), `hz' : z₀ - (w - z₀) ∉ Λ` (`by ring_nf` to `2 * z₀ - w`);
   rewrite the conclusion with the same identities.
3. `h₁ : meromorphicOrderAt ℘[L] 0 = -2 := L.order_weierstrassP 0 (zero_mem _)`.
4. `h₂ : 0 ≤ meromorphicOrderAt (fun w ↦ ℘[L] (2 * z₀ - w)) 0 := (hA.comp (analyticAt_const.sub analyticAt_id)).meromorphicOrderAt_nonneg`
   where `hA : AnalyticAt ℂ ℘[L] (2 * z₀ - 0) := L.analyticOnNhd_weierstrassP _ (by simpa using h2)`;
   `Function.comp_def` may be needed to match the lambda.
5. `rw [← meromorphicOrderAt_congr hev, h₁] at h₂; exact absurd h₂ (by decide)`.

#### Mathlib lemmas needed
`meromorphicOrderAt_congr` (Meromorphic/Order.lean:277), `AnalyticAt.meromorphicOrderAt_nonneg` (Order.lean:308),
`PeriodPair.order_weierstrassP`, `AnalyticAt.comp` (Composition.lean:859), `analyticAt_const`, `analyticAt_id`,
`ContinuousAt.preimage_mem_nhds`, `mem_nhdsWithin_of_mem_nhds`, `PeriodPair.eventually_notMem_lattice`, T004.

#### Sources
Pastras p. 13 "there is no other root" (decomposition H10; API gap resolved by T003–T005).

#### Generality decision
Any lattice; `hz₀` kept because T004 needs it.

---

### [CLEANUP-2] Final /cleanup on HalfPeriods.lean
- **Status**: done (finished 2026-09-08T17:44Z)
- **Progress**:
  - 2026-09-08T17:44: file-level cleanup complete. Stripped trailing whitespace; named the two
    remaining anonymous `have :=` bindings. 248 lines, max width 100, zero sorries, `lake build`
    clean, all declarations axiom-clean (propext/Classical.choice/Quot.sound only).
- **File**: FormalConjecturesTest/RealPeriod/HalfPeriods.lean
- **Depends on**: T005
- **Parallel**: no
- **Type**: cleanup
- **Description**: final per-file cleanup; `#print axioms PeriodPair.derivWeierstrassP_eq_zero_iff` must show only
  `propext`, `Classical.choice`, `Quot.sound`. Consider whether `Complex.isPreconnected_compl_of_countable` should be
  `private` or moved to `FormalConjecturesTest/ForMathlib`.

---

### [T006] Conjugation and reality of ℘, ℘'
- **Status**: done (finished 2026-09-08T17:52Z)
- **Progress**:
  - 2026-09-08T17:52: DONE. `Complex.conj_tsum` + reindex by `conjugateLatticeEquiv` as sketched;
    the ℘' version additionally needs `Complex.conj_ofNat` for `conj 2 = 2`. The two `coe_*Re`
    lemmas are one-line term proofs via `Complex.conj_eq_iff_re`.
- **File**: FormalConjecturesTest/RealPeriod/RealAxis.lean
- **Depends on**: T001 (for `weierstrassP_congr`, `derivWeierstrassP_congr`)
- **Parallel**: yes
- **Type**: lemmas (6 sorries: lines 70, 74, 80, 84, 100, 104)

#### Statement
```lean
lemma weierstrassP_conjugate (z : ℂ) : ℘[L.conjugate] z = conj (℘[L] (conj z)) := by sorry

lemma derivWeierstrassP_conjugate (z : ℂ) : ℘'[L.conjugate] z = conj (℘'[L] (conj z)) := by sorry

lemma IsReal.conj_weierstrassP (hL : L.IsReal) (z : ℂ) : conj (℘[L] z) = ℘[L] (conj z) := by sorry

lemma IsReal.conj_derivWeierstrassP (hL : L.IsReal) (z : ℂ) : conj (℘'[L] z) = ℘'[L] (conj z) := by sorry

lemma IsReal.coe_weierstrassPRe (hL : L.IsReal) (t : ℝ) : (L.weierstrassPRe t : ℂ) = ℘[L] t := by sorry

lemma IsReal.coe_derivWeierstrassPRe (hL : L.IsReal) (t : ℝ) :
    (L.derivWeierstrassPRe t : ℂ) = ℘'[L] t := by sorry
```

#### Proof sketch
1. `weierstrassP_conjugate`: `simp only [weierstrassP]; rw [Complex.conj_tsum, ← L.conjugateLatticeEquiv.tsum_eq];
   refine tsum_congr fun l ↦ ?_; simp [conjugateLatticeEquiv, map_sub, map_div₀, map_pow, map_one]` — template:
   `G_conjugate` (Conjugation.lean:73), which ends `ring_nf; grind`. The coercion `((conjugateLatticeEquiv L l) : ℂ) = conj l`
   is `rfl`.
2. `derivWeierstrassP_conjugate`: same with `derivWeierstrassP`, `map_neg`, `map_div₀`, `map_ofNat`.
3. `IsReal.conj_weierstrassP`: `rw [← weierstrassP_congr hL, weierstrassP_conjugate, Complex.conj_conj]` where
   `hL : L.conjugate.lattice = L.lattice` (unfold `IsReal`). Same for `℘'`.
4. `coe_weierstrassPRe`: `Complex.conj_eq_iff_re.mp` applied to `hL.conj_weierstrassP ↑t` rewritten with
   `Complex.conj_ofReal`; `weierstrassPRe` unfolds by `rfl`/`simp [weierstrassPRe]`. Same for `℘'`.

#### Mathlib lemmas needed
`Complex.conj_tsum` (Analysis/Complex/Basic.lean:590), `Equiv.tsum_eq`, `PeriodPair.conjugateLatticeEquiv`,
`map_sub`, `map_div₀`, `map_pow`, `map_one`, `map_neg`, `map_ofNat`, `Complex.conj_conj`, `Complex.conj_ofReal`,
`Complex.conj_eq_iff_re` (RCLike/Basic.lean:375), `PeriodPair.IsReal` (Conjugation.lean:104), T001 congr lemmas.

#### Sources
DLMF 23.5(i) (decomposition R1–R7).

#### Generality decision
`weierstrassP_conjugate` for every lattice; realness only where needed.

---

### [T007] Calculus of the real functions
- **Status**: done (finished 2026-09-08T17:56Z)
- **Progress**:
  - 2026-09-08T17:56: DONE, first compile. All four exactly as sketched; three are one-line terms
    via `HasDerivAt.real_of_complex`.
- **File**: FormalConjecturesTest/RealPeriod/RealAxis.lean
- **Depends on**: T002, T006
- **Parallel**: yes
- **Type**: lemmas (4 sorries: lines 111, 115, 119, 127)

#### Statement
```lean
lemma hasDerivAt_weierstrassPRe {t : ℝ} (ht : (t : ℂ) ∉ L.lattice) :
    HasDerivAt L.weierstrassPRe (L.derivWeierstrassPRe t) t := by sorry

lemma continuousAt_weierstrassPRe {t : ℝ} (ht : (t : ℂ) ∉ L.lattice) :
    ContinuousAt L.weierstrassPRe t := by sorry

lemma continuousAt_derivWeierstrassPRe {t : ℝ} (ht : (t : ℂ) ∉ L.lattice) :
    ContinuousAt L.derivWeierstrassPRe t := by sorry

lemma IsReal.derivWeierstrassPRe_sq (hL : L.IsReal) {t : ℝ} (ht : (t : ℂ) ∉ L.lattice) :
    L.derivWeierstrassPRe t ^ 2 =
      4 * L.weierstrassPRe t ^ 3 - L.g₂.re * L.weierstrassPRe t - L.g₃.re := by sorry
```

#### Proof sketch
1. `hasDerivAt_weierstrassPRe`: `exact (L.hasDerivAt_weierstrassP ht).real_of_complex` — the goal is definitionally
   `HasDerivAt (fun x : ℝ ↦ (℘[L] ↑x).re) (℘'[L] ↑t).re t`.
2. `continuousAt_weierstrassPRe := (L.hasDerivAt_weierstrassPRe ht).continuousAt`;
   `continuousAt_derivWeierstrassPRe := (L.hasDerivAt_derivWeierstrassP ht).real_of_complex.continuousAt`.
3. `derivWeierstrassPRe_sq`: `have h := L.derivWeierstrassP_sq ↑t ht`; `have h2 : L.g₂ = (L.g₂.re : ℂ) :=
   (Complex.conj_eq_iff_re.mp hL.conj_g₂).symm`, same `h3`; `rw [← hL.coe_derivWeierstrassPRe, ← hL.coe_weierstrassPRe, h2, h3] at h;
   exact_mod_cast h`.

#### Mathlib lemmas needed
`HasDerivAt.real_of_complex` (Complex/RealDeriv.lean:46), `HasDerivAt.continuousAt`, `PeriodPair.derivWeierstrassP_sq`,
`PeriodPair.IsReal.conj_g₂`, `PeriodPair.IsReal.conj_g₃` (Conjugation.lean:108,112), `Complex.conj_eq_iff_re`,
`Complex.ofReal_pow`, `Complex.ofReal_mul` (via `exact_mod_cast`), T002, T006.

#### Sources
DLMF 23.3.10 (decomposition R8–R10).

#### Generality decision
Derivative and continuity lemmas need no realness (they are about real parts).

---

### [T008] Behaviour at the pole
- **Status**: done (finished 2026-09-08T18:12Z)
- **Progress**:
  - 2026-09-08T18:12: DONE. Sketch needed three corrections, all recorded for later tickets:
    (i) `Tendsto.atTop_pow` does NOT apply to ℝ (it needs multiplicative `IsOrderedMonoid`);
    the working route is `t ^ n → 𝓝[>] 0` then `Filter.Tendsto.inv_tendsto_nhdsGT_zero`.
    (ii) `tendsto_atTop_add_left_of_le'` likewise needs `IsOrderedMonoid`; use
    `Filter.tendsto_atTop_mono'` against `tendsto_atTop_add_const_right … (-1)`.
    (iii) `simp only [heq]` cannot rewrite an eta-contracted function head — use
    `rw [show f = fun t ↦ … from funext heq]`. Also `AnalyticAt.continuousAt` must be
    `.continuousAt.tendsto` before `simpa` will see it as a `Tendsto`.
- **File**: FormalConjecturesTest/RealPeriod/RealAxis.lean
- **Depends on**: T006 (file order only; mathematically independent)
- **Parallel**: yes
- **Type**: lemmas (2 sorries: lines 137, 141)

#### Statement
```lean
lemma tendsto_weierstrassPRe_nhdsGT_zero : Tendsto L.weierstrassPRe (𝓝[>] 0) atTop := by sorry

lemma eventually_derivWeierstrassPRe_neg : ∀ᶠ t in 𝓝[>] 0, L.derivWeierstrassPRe t < 0 := by sorry
```

#### Proof sketch
1. Pointwise identities: `L.weierstrassPRe t = (℘[L - (0:ℂ)] ↑t).re + 1 / t ^ 2` from `L.weierstrassP_eq ↑t`
   (Uniqueness.lean:59) and `Complex.add_re`, `Complex.ofReal_re` after `push_cast`/`norm_cast` on `1 / (↑t)^2`;
   `L.derivWeierstrassPRe t = (℘'[L - (0:ℂ)] ↑t).re - 2 / t ^ 3` from `L.derivWeierstrassPExcept_zero_eq ↑t`
   (Uniqueness.lean:64).
2. Continuity of the regular parts at `0`: `hc : Tendsto (fun t : ℝ ↦ (℘[L - (0:ℂ)] ↑t).re) (𝓝[>] 0) (𝓝 0)` from
   `(L.analyticAt_weierstrassPExcept 0).continuousAt` (Weierstrass.lean:777), composed with `Complex.continuous_ofReal`
   and `Complex.continuous_re`, value `(℘[L - 0] 0).re = 0` (`weierstrassPExcept_zero`), restricted via
   `tendsto_nhdsWithin_of_tendsto_nhds`/`.mono_left nhdsWithin_le_nhds`. Same for `℘'[L - 0]` with
   `analyticAt_derivWeierstrassPExcept 0` (Weierstrass.lean:827) and `derivWeierstrassPExcept_zero_zero` (Weierstrass.lean:426).
3. `1 / t ^ 2 → atTop`: `(tendsto_inv_nhdsGT_zero.atTop_pow two_pos)` gives `(t⁻¹) ^ 2 → atTop`; rewrite `one_div, inv_pow`.
   Then `Filter.tendsto_atTop_add_left_of_le' (l := 𝓝[>] 0) (-1)` with `hc.eventually (eventually_ge_nhds …)` giving
   `∀ᶠ t, -1 ≤ (regular part)`, and `Tendsto.congr` with the identity of step 1.
4. `eventually_derivWeierstrassPRe_neg`: `filter_upwards [hc'.eventually (Metric.ball_mem_nhds 0 one_pos)  -- |re| < 1,
   (tendsto_inv_nhdsGT_zero.atTop_pow three_pos).eventually (eventually_gt_atTop 1)]` and finish with
   `2 / t ^ 3 = 2 * (t⁻¹)^3 > 2 > 1 > re`; `linarith` after `Real.dist_eq`/`abs_lt`.

#### Mathlib lemmas needed
`PeriodPair.weierstrassP_eq`, `PeriodPair.derivWeierstrassPExcept_zero_eq` (project), `PeriodPair.analyticAt_weierstrassPExcept`,
`PeriodPair.analyticAt_derivWeierstrassPExcept`, `PeriodPair.weierstrassPExcept_zero`,
`PeriodPair.derivWeierstrassPExcept_zero_zero`, `AnalyticAt.continuousAt`, `ContinuousAt.tendsto`, `Complex.continuous_re`,
`Complex.continuous_ofReal`, `tendsto_inv_nhdsGT_zero` (Topology/Algebra/Order/Field.lean:61), `Filter.Tendsto.atTop_pow`
(AtTopBot/Monoid.lean:85), `Filter.tendsto_atTop_add_left_of_le'` (additive of AtTopBot/Group.lean:29),
`Filter.eventually_gt_atTop`, `Filter.Tendsto.congr'`, `nhdsWithin_le_nhds`, `Complex.add_re`, `Complex.sub_re`,
`Complex.ofReal_re`, `one_div`, `inv_pow`.

#### Sources
Pastras p. 30 "as one approaches a pole from the real axis, ℘ tends to +∞" (decomposition R11, R12).

#### Generality decision
No realness hypothesis: statements about real parts hold for every lattice.

---

### [CLEANUP-3] Run /cleanup on RealAxis.lean
- **Status**: done (finished 2026-09-08T18:18Z)
- **Progress**:
  - 2026-09-08T18:18: cadence cleanup on T006-T008. Style clean (max width 100, no trailing
    whitespace, no forbidden constructs). Extracted the duplicated `t^n → 𝓝[>] 0` argument from
    the two pole lemmas into two `private` helpers `tendsto_pow_nhdsGT_zero` and
    `tendsto_inv_pow_nhdsGT_zero`, which shortened both proofs to one line each.
- **File**: FormalConjecturesTest/RealPeriod/RealAxis.lean
- **Depends on**: T008
- **Parallel**: no
- **Type**: cleanup
- **Description**: cadence cleanup after T006–T008.

---

### [T009] The least positive real period and the real half-period
- **Status**: done (finished 2026-09-08T18:24Z)
- **Progress**:
  - 2026-09-08T18:24: DONE. `notMem_lattice_of_lt` is a one-line term. In `derivWeierstrassPRe_half`
    the goal is already `(℘'[L] ↑(Ω/2)).re = 0` with the cast in the form `h` provides, so a plain
    `rw [derivWeierstrassPRe, h, Complex.zero_re]` closes it (no `push_cast` needed).
- **File**: FormalConjecturesTest/RealPeriod/RealAxis.lean
- **Depends on**: CLEANUP-3, T005
- **Parallel**: yes (with T014)
- **Type**: lemmas (3 sorries: lines 150, 154, 159). Section variable `hΩ : IsLeast {x : ℝ | (x : ℂ) ∈ L.lattice ∧ 0 < x} Ω` is `include`d.

#### Statement
```lean
lemma notMem_lattice_of_lt {t : ℝ} (h0 : 0 < t) (ht : t < Ω) : (t : ℂ) ∉ L.lattice := by sorry

lemma derivWeierstrassPRe_half : L.derivWeierstrassPRe (Ω / 2) = 0 := by sorry

lemma derivWeierstrassP_ne_zero_of_lt_half {t : ℝ} (h0 : 0 < t) (ht : t < Ω / 2) :
    ℘'[L] t ≠ 0 := by sorry
```

#### Proof sketch
1. `notMem_lattice_of_lt`: `fun hmem ↦ (hΩ.2 ⟨hmem, h0⟩).not_lt ht` (`IsLeast.2 : Ω ∈ lowerBounds S`).
2. `derivWeierstrassPRe_half`: `have := L.derivWeierstrassP_eq_zero_of_two_mul_mem (z := ((Ω / 2 : ℝ) : ℂ))
   (by rw [show (2 : ℂ) * ((Ω / 2 : ℝ) : ℂ) = (Ω : ℂ) by push_cast; ring]; exact hΩ.1.1)`;
   `simp [derivWeierstrassPRe, this]`.
3. `derivWeierstrassP_ne_zero_of_lt_half`: `intro h0'`; `hΩpos : 0 < Ω := hΩ.1.2`;
   `htL : (t : ℂ) ∉ Λ := notMem_lattice_of_lt hΩ h0 (by linarith)`;
   `h2 := L.two_mul_mem_lattice_of_derivWeierstrassP_eq_zero htL h0'`;
   `rw [show (2 : ℂ) * (t : ℂ) = ((2 * t : ℝ) : ℂ) by push_cast; ring] at h2`;
   `exact notMem_lattice_of_lt hΩ (by linarith) (by linarith) h2`.

#### Mathlib lemmas needed
`IsLeast`, `not_lt_of_le`/`LT.lt.not_le`, `Complex.ofReal_div`, `Complex.ofReal_mul`, `Complex.ofReal_ofNat`
(via `push_cast`), T001 (`derivWeierstrassP_eq_zero_of_two_mul_mem`), T005.

#### Sources
Pastras (1.35); Pastras App. A "there is no other such position on the real axis between 0 and x" (decomposition R13–R15).

#### Generality decision
No realness needed; `hΩ` is any witness of the least positive real period.

---

### [T010] Sign of ℘' and strict monotonicity of ℘ on (0, Ω/2]
- **Status**: done (finished 2026-09-08T18:30Z)
- **Progress**:
  - 2026-09-08T18:30: DONE, first compile, exactly as sketched.
- **File**: FormalConjecturesTest/RealPeriod/RealAxis.lean
- **Depends on**: T009
- **Parallel**: no
- **Type**: lemmas (2 sorries: lines 165, 170)

#### Statement
```lean
lemma IsReal.derivWeierstrassPRe_neg_of_lt_half (hL : L.IsReal) {t : ℝ} (h0 : 0 < t)
    (ht : t < Ω / 2) : L.derivWeierstrassPRe t < 0 := by sorry

lemma IsReal.strictAntiOn_weierstrassPRe (hL : L.IsReal) :
    StrictAntiOn L.weierstrassPRe (Ioc 0 (Ω / 2)) := by sorry
```

#### Proof sketch
1. `derivWeierstrassPRe_neg_of_lt_half`: `by_contra hge; push_neg at hge` (`0 ≤ d t`). `hne : d t ≠ 0`: from
   `derivWeierstrassP_ne_zero_of_lt_half hΩ h0 ht` and `hL.coe_derivWeierstrassPRe t` (`Complex.ofReal_eq_zero`).
   So `hpos : 0 < d t`. Get `t₁` with `0 < t₁ < t` and `d t₁ < 0`:
   `obtain ⟨t₁, ht₁neg, ht₁⟩ := (L.eventually_derivWeierstrassPRe_neg.and (Ioo_mem_nhdsGT h0)).exists`.
   Continuity on `Icc t₁ t`: `fun x hx ↦ (L.continuousAt_derivWeierstrassPRe (notMem_lattice_of_lt hΩ (by linarith [hx.1]) (by linarith [hx.2, hΩ.1.2]))).continuousWithinAt`.
   `obtain ⟨t₂, ht₂, h0'⟩ := intermediate_value_Ioo ht₁.2.le hcont ⟨ht₁neg, hpos⟩` (`0 ∈ Ioo (d t₁) (d t)`).
   Contradiction: `derivWeierstrassP_ne_zero_of_lt_half hΩ (by linarith [ht₂.1]) (by linarith [ht₂.2])` with
   `℘'[L] ↑t₂ = ↑(d t₂) = 0` via `hL.coe_derivWeierstrassPRe`.
2. `strictAntiOn_weierstrassPRe`: `refine strictAntiOn_of_deriv_neg (convex_Ioc 0 (Ω / 2)) ?_ ?_`.
   Continuity: `fun x hx ↦ (L.continuousAt_weierstrassPRe (notMem_lattice_of_lt hΩ hx.1 (by linarith [hx.2, hΩ.1.2]))).continuousWithinAt`.
   Derivative: `intro x hx; rw [interior_Ioc] at hx; rw [(L.hasDerivAt_weierstrassPRe (notMem_lattice_of_lt hΩ hx.1 (by linarith [hx.2, hΩ.1.2]))).deriv];
   exact hL.derivWeierstrassPRe_neg_of_lt_half hΩ hx.1 hx.2`.

#### Mathlib lemmas needed
`intermediate_value_Ioo` (IntermediateValue.lean:643), `Ioo_mem_nhdsGT`, `Filter.Eventually.and`, `Filter.Eventually.exists`,
`strictAntiOn_of_deriv_neg` (Deriv/MeanValue.lean:443), `convex_Ioc`, `interior_Ioc` (DenselyOrdered.lean:139),
`HasDerivAt.deriv`, `ContinuousAt.continuousWithinAt`, `Complex.ofReal_eq_zero`, T007, T008, T009.

#### Sources
Pastras p. 30 (monotonicity between pole and half-period) (decomposition R16, R17).

#### Generality decision
Realness `hL` needed (values of ℘' must be real to compare signs).

---

### [T011] The image of (0, Ω/2)
- **Status**: done (finished 2026-09-08T18:34Z)
- **Progress**:
  - 2026-09-08T18:34: DONE, first compile, as sketched.
- **File**: FormalConjecturesTest/RealPeriod/RealAxis.lean
- **Depends on**: T010
- **Parallel**: no
- **Type**: lemma (1 sorry: line 175)

#### Statement
```lean
lemma IsReal.image_weierstrassPRe_Ioo (hL : L.IsReal) :
    L.weierstrassPRe '' Ioo 0 (Ω / 2) = Ioi (L.weierstrassPRe (Ω / 2)) := by sorry
```

#### Proof sketch
1. `refine subset_antisymm ?_ ?_`.
2. `⊆`: `rintro _ ⟨t, ht, rfl⟩; exact (hL.strictAntiOn_weierstrassPRe hΩ) ⟨ht.1, ht.2.le⟩ ⟨half_pos hΩ.1.2, le_rfl⟩ ht.2`
   (`StrictAntiOn f s : a ∈ s → b ∈ s → a < b → f b < f a`; result is `mem_Ioi`).
3. `⊇`: `intro y hy` (`hy : e < y`). Choose `t'`:
   `obtain ⟨t', hyt', ht'⟩ := ((L.tendsto_weierstrassPRe_nhdsGT_zero.eventually (eventually_gt_atTop y)).and
   (Ioo_mem_nhdsGT (half_pos hΩ.1.2))).exists` — `t' ∈ Ioo 0 (Ω/2)`, `y < f t'`.
   Continuity on `Icc t' (Ω/2)` as in T010 (points `≤ Ω/2 < Ω`).
   `obtain ⟨t, ht, rfl⟩ := intermediate_value_Ioo' ht'.2.le hcont ⟨hy, hyt'⟩`; `exact ⟨t, ⟨by linarith [ht'.1, ht.1], ht.2⟩, rfl⟩`.

#### Mathlib lemmas needed
`intermediate_value_Ioo'` (IntermediateValue.lean:652: `Ioo (f b) (f a) ⊆ f '' Ioo a b`), `Filter.Tendsto.eventually`,
`Filter.eventually_gt_atTop`, `Ioo_mem_nhdsGT`, `StrictAntiOn`, `Set.subset_antisymm`, `half_pos`, T008, T009, T010.

#### Sources
Pastras p. 30 "each value appears once in [0, ω₁]" (decomposition R18).

#### Generality decision
As stated; `Ω/2` endpoint value is `e₁`.

---

### [CLEANUP-4] Run /cleanup on RealAxis.lean
- **Status**: done (finished 2026-09-08T18:36Z)
- **Progress**:
  - 2026-09-08T18:36: cadence cleanup on T009-T011. Style scan clean (max width 100, no trailing
    whitespace, no forbidden constructs, all bodies ≤ 20 lines). The `hne` helper inside
    `derivWeierstrassPRe_neg_of_lt_half` is used twice, so it stays as a local `have`. No golf
    opportunities left: every proof is already the shortest form that compiles.
- **File**: FormalConjecturesTest/RealPeriod/RealAxis.lean
- **Depends on**: T011
- **Parallel**: no
- **Type**: cleanup
- **Description**: cadence cleanup after T009–T011.

---

### [T012] ℘(Ω/2) is the largest real root
- **Status**: done (finished 2026-09-08T18:42Z)
- **Progress**:
  - 2026-09-08T18:42: DONE. Needed `(t := Ω / 2)` explicitly on `derivWeierstrassPRe_sq` (Lean
    otherwise unifies `t := Ω` from the `notMem_lattice_of_lt` argument). `push_neg` is deprecated
    in this Mathlib — `push Not` used instead.
- **File**: FormalConjecturesTest/RealPeriod/RealAxis.lean
- **Depends on**: CLEANUP-4
- **Parallel**: yes (with T013 only after this; with T014)
- **Type**: lemmas (2 sorries: lines 180, 187)

#### Statement
```lean
lemma IsReal.isRoot_weierstrassPRe_half (hL : L.IsReal) :
    4 * L.weierstrassPRe (Ω / 2) ^ 3 - L.g₂.re * L.weierstrassPRe (Ω / 2) - L.g₃.re = 0 := by sorry

lemma IsReal.le_weierstrassPRe_half_of_isRoot (hL : L.IsReal) {x : ℝ}
    (hx : 4 * x ^ 3 - L.g₂.re * x - L.g₃.re = 0) : x ≤ L.weierstrassPRe (Ω / 2) := by sorry
```

#### Proof sketch
1. `isRoot`: `have h := hL.derivWeierstrassPRe_sq (notMem_lattice_of_lt hΩ (half_pos hΩ.1.2) (by linarith [hΩ.1.2]))`;
   `rw [derivWeierstrassPRe_half hΩ] at h; linarith` (or `simpa using h.symm`).
2. `le_of_isRoot`: `by_contra hlt; push_neg at hlt`; `obtain ⟨t, ht, hxt⟩ := (hL.image_weierstrassPRe_Ioo hΩ).symm ▸ (mem_Ioi.mpr hlt)`
   (i.e. `x ∈ Ioi e = f '' Ioo`); `have h := hL.derivWeierstrassPRe_sq (notMem_lattice_of_lt hΩ ht.1 (by linarith [ht.2, hΩ.1.2]))`;
   `rw [hxt, hx] at h` (`d t ^ 2 = 0`); `exact (hL.derivWeierstrassPRe_neg_of_lt_half hΩ ht.1 ht.2).ne (pow_eq_zero_iff two_ne_zero |>.mp h)`.

#### Mathlib lemmas needed
`pow_eq_zero_iff`, `Set.mem_Ioi`, `Set.mem_image`, `half_pos`, `LT.lt.ne`, T007, T009, T010, T011.

#### Sources
Pastras (1.36); DLMF 23.5.1 / 23.5(iv) (decomposition R19, R20).

#### Generality decision
Cubic written with `L.g₂.re`, `L.g₃.re`; no case split on Δ.

---

### [T013] The elliptic integral equals Ω/2
- **Status**: done (finished 2026-09-08T18:48Z)
- **Progress**:
  - 2026-09-08T18:48: DONE, first compile, exactly as sketched (`f'` had to be given explicitly).
    RealAxis.lean is now sorry-free; `integral_inv_sqrt_eq_half` is axiom-clean.
- **File**: FormalConjecturesTest/RealPeriod/RealAxis.lean
- **Depends on**: T012
- **Parallel**: no
- **Type**: lemmas (2 sorries: lines 193, 202)

#### Statement
```lean
lemma IsReal.abs_derivWeierstrassPRe_mul_inv_sqrt (hL : L.IsReal) {t : ℝ} (h0 : 0 < t)
    (ht : t < Ω / 2) : |L.derivWeierstrassPRe t| *
      (√(4 * L.weierstrassPRe t ^ 3 - L.g₂.re * L.weierstrassPRe t - L.g₃.re))⁻¹ = 1 := by sorry

theorem IsReal.integral_inv_sqrt_eq_half (hL : L.IsReal) :
    ∫ x in Ioi (L.weierstrassPRe (Ω / 2)), (√(4 * x ^ 3 - L.g₂.re * x - L.g₃.re))⁻¹ = Ω / 2 := by sorry
```

#### Proof sketch
1. `abs_…`: `rw [← hL.derivWeierstrassPRe_sq (notMem_lattice_of_lt hΩ h0 (by linarith [hΩ.1.2])), Real.sqrt_sq_eq_abs];
   exact mul_inv_cancel₀ (abs_ne_zero.mpr (hL.derivWeierstrassPRe_neg_of_lt_half hΩ h0 ht).ne)`.
2. `integral`: `rw [← hL.image_weierstrassPRe_Ioo hΩ]`;
   `rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo (fun x hx ↦ (L.hasDerivAt_weierstrassPRe
   (notMem_lattice_of_lt hΩ hx.1 (by linarith [hx.2, hΩ.1.2]))).hasDerivWithinAt)
   ((hL.strictAntiOn_weierstrassPRe hΩ).injOn.mono Ioo_subset_Ioc_self)]`;
   `rw [setIntegral_congr_fun measurableSet_Ioo (g := fun _ ↦ (1 : ℝ)) (fun x hx ↦ by
   simpa [smul_eq_mul] using hL.abs_derivWeierstrassPRe_mul_inv_sqrt hΩ hx.1 hx.2)]`;
   `rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [hΩ.1.2]), smul_eq_mul, mul_one, sub_zero]`.

Bridging: the `f'` argument of `integral_image_eq_integral_abs_deriv_smul` is implicit — supply `(f' := L.derivWeierstrassPRe)`
if unification stalls; `Real.volume_real_Ioo_of_le` may be stated with `volume.real` — if the goal shows
`(volume (Ioo 0 (Ω/2))).toReal`, use `Real.volume_Ioo` + `ENNReal.toReal_ofReal`.

#### Mathlib lemmas needed
`MeasureTheory.integral_image_eq_integral_abs_deriv_smul` (JacobianOneDim.lean:66), `MeasureTheory.setIntegral_congr_fun`
(Bochner/Set.lean:73), `MeasureTheory.setIntegral_const` (Bochner/Set.lean:527), `Real.volume_real_Ioo_of_le`
(Lebesgue/Basic.lean:106), `Real.sqrt_sq_eq_abs` (Real/Sqrt.lean:189), `StrictAntiOn.injOn` (Order/Monotone/Basic.lean:415),
`Set.InjOn.mono`, `Set.Ioo_subset_Ioc_self`, `HasDerivAt.hasDerivWithinAt`, `measurableSet_Ioo`, `mul_inv_cancel₀`,
`abs_ne_zero`, `smul_eq_mul`, T007, T010, T011, T012.

#### Sources
DLMF 23.6.34, 23.6.36; Pastras (1.31)–(1.32), (3.1), (A.1) (decomposition R21, R21b).

#### Generality decision
Any real lattice and any witness `Ω` of the least positive real period; conclusion is the integral over `Ioi e₁` as
a set integral (matches `leastRealPeriodIntegral`'s form).

---

### [CLEANUP-5] Final /cleanup on RealAxis.lean
- **Status**: done (finished 2026-09-08T18:50Z)
- **Progress**:
  - 2026-09-08T18:50: final per-file cleanup. Repacked one 101-char line. 337 lines, max width 100,
    no trailing whitespace, zero sorries, `lake build` clean, axioms clean.
- **File**: FormalConjecturesTest/RealPeriod/RealAxis.lean
- **Depends on**: T013
- **Parallel**: no
- **Type**: cleanup
- **Description**: final per-file cleanup; `#print axioms PeriodPair.IsReal.integral_inv_sqrt_eq_half`.

---

### [T014] Invariants of the period lattice of a curve
- **Status**: done (finished 2026-09-08T18:55Z)
- **Progress**:
  - 2026-09-08T18:55: DONE, first compile, as sketched.
- **File**: FormalConjecturesTest/RealPeriodIntegral.lean
- **Depends on**: none
- **Parallel**: yes
- **Type**: lemmas (4 sorries: lines 54, 58, 63, 66)

#### Statement
```lean
lemma periodPair_g₂ (W : WeierstrassCurve ℂ) [W.IsElliptic] : W.periodPair.g₂ = W.c₄ / 12 := by sorry

lemma periodPair_g₃ (W : WeierstrassCurve ℂ) [W.IsElliptic] : W.periodPair.g₃ = W.c₆ / 216 := by sorry

lemma periodPair_map_g₂_re : (W.map Complex.ofRealHom).periodPair.g₂.re = W.c₄ / 12 := by sorry

lemma periodPair_map_g₃_re : (W.map Complex.ofRealHom).periodPair.g₃.re = W.c₆ / 216 := by sorry
```
(`W : WeierstrassCurve ℝ` `[W.IsElliptic]` is a section variable for the last two.)

#### Proof sketch
1. `periodPair_g₂`: `have h := (PeriodPair.exists_g₂_g₃ W.shortModel_discr_ne_zero).choose_spec;`
   `show (PeriodPair.exists_g₂_g₃ W.shortModel_discr_ne_zero).choose.g₂ = _` (unfold `periodPair`, `PeriodPair.ofCoeffs`);
   `rw [h.1]; ring`. Same for `g₃` with `h.2`.
2. `periodPair_map_g₂_re`: `rw [periodPair_g₂, map_c₄, Complex.ofRealHom_eq_coe]`, then
   `rw [show ((W.c₄ : ℂ) / 12) = ((W.c₄ / 12 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]`. Same for `c₆`/`216`.
   (See `periodPair_map_isReal` in `RealPeriod.lean` for the same rewrites.)

#### Mathlib lemmas needed
`PeriodPair.exists_g₂_g₃` (Existence.lean:225), `WeierstrassCurve.shortModel_discr_ne_zero`, `PeriodPair.ofCoeffs`,
`WeierstrassCurve.periodPair` (RealPeriod.lean), `WeierstrassCurve.map_c₄`, `WeierstrassCurve.map_c₆`,
`Complex.ofRealHom_eq_coe`, `Complex.ofReal_re`, `Complex.ofReal_div` (via `push_cast`).

#### Sources
Project `RealPeriod.lean` docstring; Existence.lean `weierstrassCurve_c₄` (decomposition F1, F2).

#### Generality decision
`periodPair_g₂/g₃` over ℂ for any elliptic `W` (not only real ones).

---

### [T015] The largest root under the depressing substitution
- **Status**: done (finished 2026-09-08T19:02Z)
- **Progress**:
  - 2026-09-08T19:02: DONE. One subtlety: `have hL : L.IsReal := …` makes the realness proof
    opaque, so `L.isLeast_leastRealPeriod hL` displays `L.leastRealPeriod hL` while the goal has
    `W.leastRealPeriod`; they are definitionally equal (proof irrelevance), so ascribing the
    explicit type `IsLeast {x | ↑x ∈ L.lattice ∧ 0 < x} W.leastRealPeriod` to `hΩ` fixes it.
- **File**: FormalConjecturesTest/RealPeriodIntegral.lean
- **Depends on**: T013, T014
- **Parallel**: no
- **Type**: lemma (1 sorry: line 73)

#### Statement
```lean
lemma e₁_add_b₂_div_twelve : W.e₁ + W.b₂ / 12 =
    (W.map Complex.ofRealHom).periodPair.weierstrassPRe (W.leastRealPeriod / 2) := by sorry
```

#### Proof sketch
1. `set L := (W.map Complex.ofRealHom).periodPair; have hL := W.periodPair_map_isReal;
   have hΩ := L.isLeast_leastRealPeriod hL` (note `W.leastRealPeriod = L.leastRealPeriod hL` by `rfl`);
   `set e := L.weierstrassPRe (W.leastRealPeriod / 2)`.
2. `have hroot := hL.isRoot_weierstrassPRe_half hΩ; have hmax := fun x hx ↦ hL.le_weierstrassPRe_half_of_isRoot hΩ (x := x) hx;
   rw [W.periodPair_map_g₂_re, W.periodPair_map_g₃_re] at hroot hmax`.
3. `have key : W.e₁ = e - W.b₂ / 12 := W.e₁_eq_of_isRoot ?_ ?_`.
   - root: `rw [Polynomial.IsRoot, W.eval_toPoly_twoTorsionPolynomial_sub]; exact hroot`
     (`eval_toPoly_twoTorsionPolynomial_sub x : F.eval (x - b₂/12) = 4x³ - c₄/12 x - c₆/216`).
   - maximal: `intro x hx hroot'`; `have := hmax (x + W.b₂ / 12) (by rw [← W.eval_toPoly_twoTorsionPolynomial_sub,
     add_sub_cancel_right]; exact hroot')`; `linarith`.
4. `linarith [key]` (or `rw [key]; ring`).

#### Mathlib lemmas needed
`WeierstrassCurve.e₁_eq_of_isRoot`, `WeierstrassCurve.eval_toPoly_twoTorsionPolynomial_sub` (PeriodIntegral.lean),
`WeierstrassCurve.periodPair_map_isReal`, `PeriodPair.isLeast_leastRealPeriod` (RealPeriod.lean), `Polynomial.IsRoot`,
`add_sub_cancel_right`, T012, T014.

#### Sources
PeriodIntegral.lean docstring (substitution `x = X − b₂/12`); DLMF 23.5(ii)/(iv) (decomposition F3).

#### Generality decision
Stated with `W.leastRealPeriod` (the project's definition) on the right so that T016 is a rewrite.

---

### [CLEANUP-ALL-1] Run /cleanup-all on the project so far
- **Status**: done (finished 2026-09-08T19:04Z)
- **Progress**:
  - 2026-09-08T19:04: pre-milestone project-wide check. All three files build clean; HalfPeriods
    and RealAxis are sorry-free with max width 100 and no trailing whitespace; every finished
    declaration is axiom-clean. RealPeriodIntegral has only the two milestone sorries left.
- **File**: all three files
- **Depends on**: CLEANUP-2, CLEANUP-5, T015
- **Parallel**: no
- **Type**: cleanup
- **Description**: project-wide cleanup before the milestone.

---

### [T016] MILESTONE — the two real periods agree
- **Status**: done (finished 2026-09-08T19:10Z)
- **Progress**:
  - 2026-09-08T19:10: DONE — `leastRealPeriodIntegral_eq_leastRealPeriod` and
    `realPeriodIntegral_eq_realPeriod` are proved, sorry-free, axioms
    propext/Classical.choice/Quot.sound only. Same `IsLeast` type-ascription trick as T015.
- **File**: FormalConjecturesTest/RealPeriodIntegral.lean
- **Depends on**: CLEANUP-ALL-1
- **Parallel**: no
- **Type**: theorem (2 sorries: lines 82, 87)

#### Statement
```lean
theorem leastRealPeriodIntegral_eq_leastRealPeriod :
    W.leastRealPeriodIntegral = W.leastRealPeriod := by sorry

theorem realPeriodIntegral_eq_realPeriod : W.realPeriodIntegral = W.realPeriod := by sorry
```

#### Proof sketch
1. `rw [W.leastRealPeriodIntegral_eq_integral_depressed, W.e₁_add_b₂_div_twelve]`.
2. `rw [← W.periodPair_map_g₂_re, ← W.periodPair_map_g₃_re]` (turn `c₄/12`, `c₆/216` into `L.g₂.re`, `L.g₃.re`;
   if `rw` fails to find the pattern inside the integrand lambda, use `simp only [← …]` or `show` with the explicit
   integrand).
3. `rw [(W.periodPair_map_isReal).integral_inv_sqrt_eq_half (PeriodPair.isLeast_leastRealPeriod _ _)]; ring`.
4. `realPeriodIntegral_eq_realPeriod`: `rw [realPeriodIntegral, realPeriod, W.leastRealPeriodIntegral_eq_leastRealPeriod]`.
5. Verify: `#print axioms WeierstrassCurve.realPeriodIntegral_eq_realPeriod` → only `propext`, `Classical.choice`, `Quot.sound`.

#### Mathlib lemmas needed
`WeierstrassCurve.leastRealPeriodIntegral_eq_integral_depressed` (PeriodIntegral.lean), `PeriodPair.isLeast_leastRealPeriod`,
`WeierstrassCurve.periodPair_map_isReal`, T013, T014, T015.

#### Sources
DLMF 23.6.34/36; Cremona §3.7 (decomposition R1, R2).

#### Generality decision
`[W.IsElliptic]` only, matching both definitions.

---

### [CLEANUP-6] Final /cleanup on RealPeriodIntegral.lean
- **Status**: done (finished 2026-09-08T19:12Z)
- **Progress**:
  - 2026-09-08T19:12: 119 lines, max width 99, no trailing whitespace, both public theorems have
    docstrings. Also updated the now-stale sentence in PeriodIntegral.lean's module docstring
    ("That the two versions agree is the uniformisation theorem, which is not proved here") to
    point at `FormalConjecturesTest.RealPeriodIntegral`; the file still builds.
- **File**: FormalConjecturesTest/RealPeriodIntegral.lean
- **Depends on**: T016
- **Parallel**: no
- **Type**: cleanup
- **Description**: final per-file cleanup. Also decide (ask the user) whether to update the sentence "That the two
  versions agree is the uniformisation theorem, which is not proved here" in `PeriodIntegral.lean`'s docstring to
  point at `FormalConjecturesTest.RealPeriodIntegral`.

---

### [CLEANUP-FINAL] Run /cleanup-all on the whole project
- **Status**: done (finished 2026-09-08T19:14Z)
- **File**: all
- **Depends on**: CLEANUP-6
- **Parallel**: no
- **Type**: cleanup
- **Description**: final pass; then `/pre-submit`.

## Cleanup cadence check
16 proof/definition tickets → ⌈16/3⌉ = 6 cleanups required; present: CLEANUP-1 (after T003), CLEANUP-2 (final HalfPeriods),
CLEANUP-3 (after T008), CLEANUP-4 (after T011), CLEANUP-5 (final RealAxis), CLEANUP-6 (final RealPeriodIntegral, also the
3rd-ticket point of that file), CLEANUP-ALL-1 (pre-milestone), CLEANUP-FINAL. ✓
