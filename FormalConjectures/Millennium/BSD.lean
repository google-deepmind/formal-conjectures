/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib

/-!
# The weak Birch and Swinnerton-Dyer conjecture: two equivalent forms

Self-contained single file: it only imports `Mathlib` (it needs a Mathlib recent enough to have
`WeierstrassCurve.LSeries`, from `Mathlib/AlgebraicGeometry/EllipticCurve/LFunction.lean`; checked
with Lean `v4.35.0-rc3` and Mathlib master `aaf410c`). The parts that in the
formal-conjectures repository come from `FormalConjecturesUtil` and
`FormalConjectures.Wikipedia.HasseWeil` are copied here, and the `@[category ...]`/`@[AMS ...]`
attributes (which only exist in that repository) are dropped.

**No `sorry` in this file.** The Birch and Swinnerton-Dyer conjecture is an open problem (a Clay
Millennium Problem), so it is *stated* as the propositions `BSD.Weak` and `BSD.WeakAnalytic`
(definitions of `Prop`), never claimed as a theorem. What is *proved* here:

* `AddCommGroup.freeRank_eq_finrank`: for a finitely generated abelian group, Mathlib's
  `AddCommGroup.freeRank` equals `Module.finrank ℤ`.
* `BSD.WeakAnalytic.weak : WeakAnalytic K → Weak K` (no extra hypotheses).
* `BSD.Weak.weakAnalytic`, `BSD.weak_iff_weakAnalytic`: the converse and the equivalence,
  *conditional* on the Hasse--Weil continuation and the Mordell--Weil theorem, passed as explicit
  hypotheses (both are known theorems over `ℚ`, but are not in Mathlib).

Both forms use Mathlib's own `WeierstrassCurve.LSeries` (Euler product built from
`Reduction.lean`/`LFunction.lean`), so no new notion of minimal model, `a_p` or Euler product is
introduced. `WeakAnalytic ℚ` is the statement in Wiles' official Clay description: `L(E, s)` has a
holomorphic continuation whose Taylor expansion at `s = 1` is `c (s - 1)^r + ⋯` with `c ≠ 0` and
`r = rank E(ℚ)`. Over `ℚ` it is a reformulation of `Weak ℚ`, not a new problem.

*References:*
- [Clay] A. Wiles, official problem description,
  [claymath.org](https://www.claymath.org/wp-content/uploads/2022/05/birchswin.pdf)
- [Tate1966] J. Tate, "On the conjectures of Birch and Swinnerton-Dyer and a geometric analog",
  Séminaire Bourbaki, Exp. 306 (1966).
- [Gross2011] B. H. Gross, "Lectures on the conjecture of Birch and Swinnerton-Dyer",
  IAS/Park City Math. Ser. 18 (2011), Conjecture 2.10.
-/

open Module

/-! ## The free rank of a finitely generated abelian group -/

/-- The free rank of a finitely generated abelian group is its `ℤ`-rank. -/
theorem AddCommGroup.freeRank_eq_finrank (G : Type*) [AddCommGroup G] [AddGroup.FG G] :
    AddCommGroup.freeRank G = finrank ℤ G := by
  set Q := G ⧸ Submodule.torsion ℤ G
  let e : (G ⧸ AddCommGroup.torsion G) ≃+ Q :=
    QuotientAddGroup.congr _ _ (AddEquiv.refl G) (by simp [← Submodule.torsion_int])
  have : Module.Finite ℤ G := Module.Finite.iff_addGroup_fg.mpr inferInstance
  have hFG : AddGroup.FG Q := Module.Finite.iff_addGroup_fg.mp inferInstance
  rw [AddCommGroup.freeRank_def, AddGroup.rank_congr e,
    ← finrank_quotient_eq_of_le_torsion le_rfl]
  have hspan (s : Set Q) : (Submodule.span ℤ s).toAddSubgroup = AddSubgroup.closure s :=
    Submodule.span_int_eq_addSubgroupClosure s
  apply le_antisymm
  · let b := Module.Free.chooseBasis ℤ Q
    classical
    calc AddGroup.rank Q ≤ (Finset.univ.image b).card := by
          apply AddGroup.rank_le
          rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, ← hspan, b.span_eq]
          rfl
      _ ≤ Finset.univ.card := Finset.card_image_le
      _ = finrank ℤ Q := by rw [Finset.card_univ, Module.finrank_eq_card_chooseBasisIndex]
  · obtain ⟨S, hS, hcl⟩ := AddGroup.rank_spec Q
    rw [← hS]
    have htop : Submodule.span ℤ (S : Set Q) = ⊤ := by
      apply Submodule.toAddSubgroup_injective
      rw [hspan, hcl]
      rfl
    calc finrank ℤ Q = finrank ℤ (⊤ : Submodule ℤ Q) := (finrank_top ℤ Q).symm
      _ = finrank ℤ (Submodule.span ℤ (S : Set Q)) := by rw [htop]
      _ ≤ S.card := finrank_span_finset_le_card S

/-! ## Continuations of the `L`-series (copied from formal-conjectures `HasseWeil.lean`) -/

namespace HasseWeil

variable {K : Type*} [Field K] [NumberField K] {E : WeierstrassCurve K}

/-- The `L`-series of `E` has the meromorphic continuation `L`: `L` is meromorphic on `ℂ` and
agrees with `E.LSeries` on `Re s > 3/2`, where the series converges absolutely. -/
def HasMeromorphicContinuation (E : WeierstrassCurve K) (L : ℂ → ℂ) : Prop :=
  Meromorphic L ∧ ∀ s : ℂ, 3 / 2 < s.re → L s = E.LSeries s

/-- The `L`-series of `E` has the analytic continuation `L`: `L` is analytic on `ℂ` and agrees
with `E.LSeries` on `Re s > 3/2`. -/
def HasAnalyticContinuation (E : WeierstrassCurve K) (L : ℂ → ℂ) : Prop :=
  (∀ z, AnalyticAt ℂ L z) ∧ ∀ s : ℂ, 3 / 2 < s.re → L s = E.LSeries s

/-- An analytic continuation is a meromorphic continuation. -/
theorem HasAnalyticContinuation.hasMeromorphicContinuation {L : ℂ → ℂ}
    (hL : HasAnalyticContinuation E L) : HasMeromorphicContinuation E L :=
  ⟨fun z ↦ (hL.1 z).meromorphicAt, hL.2⟩

open scoped Topology in
/-- Two meromorphic continuations of the `L`-series of `E` agree on a punctured neighbourhood of
every point. -/
theorem HasMeromorphicContinuation.unique {L L' : ℂ → ℂ}
    (hL : HasMeromorphicContinuation E L) (hL' : HasMeromorphicContinuation E L') (x : ℂ) :
    L =ᶠ[𝓝[≠] x] L' := by
  have h2 : meromorphicOrderAt (L - L') 2 = ⊤ := meromorphicOrderAt_eq_top_iff.2 <|
    Filter.eventually_of_mem (nhdsWithin_le_nhds <| (Complex.isOpen_re_gt (3 / 2)).mem_nhds
      (by norm_num)) fun s hs ↦ sub_eq_zero.2 ((hL.2 s hs).trans (hL'.2 s hs).symm)
  have key : meromorphicOrderAt (L - L') x = ⊤ := not_not.1 fun hx ↦
    (hL.1.sub hL'.1).exists_meromorphicOrderAt_ne_top_iff_forall.1 ⟨x, hx⟩ 2 h2
  exact (meromorphicOrderAt_eq_top_iff.1 key).mono fun s hs ↦ sub_eq_zero.1 hs

end HasseWeil

/-! ## The two forms of the weak BSD conjecture -/

namespace BSD

open HasseWeil

/-- **Weak Birch and Swinnerton-Dyer conjecture** for a number field `K` (statement only, open
problem; [Tate1966], Conjecture (A); [Gross2011], Conjecture 2.10): for every elliptic curve `E`
over `K` with `E(K)` finitely generated (Mordell--Weil, not in Mathlib, hence a hypothesis), every
meromorphic continuation `L` of its `L`-series has order `rank E(K)` at `s = 1`. -/
def Weak (K : Type*) [Field K] [NumberField K] [DecidableEq K] : Prop :=
  ∀ (E : WeierstrassCurve K) [E.IsElliptic] [AddGroup.FG E.toAffine.Point] (L : ℂ → ℂ),
    HasMeromorphicContinuation E L →
      meromorphicOrderAt L 1 = AddCommGroup.freeRank E.toAffine.Point

/-- **Weak Birch and Swinnerton-Dyer conjecture**, analytic form (statement only, open problem;
the form of Wiles' Clay description): for every elliptic curve `E` over `K`, the `L`-series of `E`
has an analytic continuation `L` to `ℂ` whose order of vanishing at `s = 1` is a natural number `r`
(so `c ≠ 0` in `c (s - 1)^r + ⋯`), and `rank_ℤ E(K) = r`. The rank is `Module.rank`, so the
statement also asserts that it is finite; no `AddGroup.FG` hypothesis is needed. -/
def WeakAnalytic (K : Type*) [Field K] [NumberField K] [DecidableEq K] : Prop :=
  ∀ (E : WeierstrassCurve K) [E.IsElliptic], ∃ L : ℂ → ℂ, HasAnalyticContinuation E L ∧
    ∃ r : ℕ, analyticOrderAt L 1 = r ∧ Module.rank ℤ E.toAffine.Point = r

variable {K : Type*} [Field K] [NumberField K] [DecidableEq K]

/-- The analytic form implies the weak BSD conjecture, with no further hypotheses. -/
theorem WeakAnalytic.weak (h : WeakAnalytic K) : Weak K := by
  intro E _ _ L hL
  obtain ⟨L', hL', r, hr, hrank⟩ := h E
  have hfin : Module.finrank ℤ E.toAffine.Point = r := Module.finrank_eq_of_rank_eq hrank
  rw [meromorphicOrderAt_congr (hL.unique hL'.hasMeromorphicContinuation 1),
    (hL'.1 1).meromorphicOrderAt_eq, hr, AddCommGroup.freeRank_eq_finrank, hfin]
  simp

/-- The weak BSD conjecture implies the analytic form, assuming the Hasse--Weil continuation
`hHW` and the Mordell--Weil theorem `hMW` for `K` (conditional result). -/
theorem Weak.weakAnalytic
    (hHW : ∀ (E : WeierstrassCurve K) [E.IsElliptic], ∃ L, HasAnalyticContinuation E L)
    (hMW : ∀ (E : WeierstrassCurve K) [E.IsElliptic], Module.Finite ℤ E.toAffine.Point)
    (h : Weak K) : WeakAnalytic K := by
  intro E _
  obtain ⟨L, hL⟩ := hHW E
  have : AddGroup.FG E.toAffine.Point := Module.Finite.iff_addGroup_fg.mp (hMW E)
  have key := h E L hL.hasMeromorphicContinuation
  rw [(hL.1 1).meromorphicOrderAt_eq, AddCommGroup.freeRank_eq_finrank] at key
  refine ⟨L, hL, Module.finrank ℤ E.toAffine.Point, ?_, (Module.finrank_eq_rank _ _).symm⟩
  cases hn : analyticOrderAt L 1 with
  | top => simp [hn] at key
  | coe n => simp_all

/-- Given the Hasse--Weil continuation and the Mordell--Weil theorem for `K`, the weak BSD
conjecture is equivalent to its analytic form (conditional result). -/
theorem weak_iff_weakAnalytic
    (hHW : ∀ (E : WeierstrassCurve K) [E.IsElliptic], ∃ L, HasAnalyticContinuation E L)
    (hMW : ∀ (E : WeierstrassCurve K) [E.IsElliptic], Module.Finite ℤ E.toAffine.Point) :
    Weak K ↔ WeakAnalytic K :=
  ⟨Weak.weakAnalytic hHW hMW, WeakAnalytic.weak⟩

end BSD

#print axioms BSD.weak_iff_weakAnalytic

