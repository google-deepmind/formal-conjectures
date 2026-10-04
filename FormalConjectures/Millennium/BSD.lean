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
module

public import FormalConjecturesUtil
public import FormalConjectures.Wikipedia.HasseWeil


/-!
# The Birch and Swinnerton-Dyer (BSD) Conjecture

*References:*
- [The Clay Institute](https://www.claymath.org/millennium/birch-and-swinnerton-dyer-conjecture/),
  official problem description by Andrew Wiles:
  [claymath.org](https://www.claymath.org/wp-content/uploads/2022/05/birchswin.pdf)
- [BSD1965] B. J. Birch and H. P. F. Swinnerton-Dyer. "Notes on elliptic curves. II."
  Journal fur die reine und angewandte Mathematik 218 (1965), 79-108,
  [doi](https://doi.org/10.1515/crll.1965.218.79)
- [Tate1966] John Tate. "On the conjectures of Birch and Swinnerton-Dyer and a geometric analog."
  Seminaire Bourbaki, Vol. 9, Exp. No. 306 (1966), 415-440,
  [numdam](https://www.numdam.org/item/SB_1964-1966__9__415_0/)
- [Gross2011] Benedict H. Gross. "Lectures on the conjecture of Birch and Swinnerton-Dyer."
  Arithmetic of L-functions, IAS/Park City Math. Ser. 18, AMS (2011), 169-209,
  [math.harvard.edu](https://people.math.harvard.edu/~gross/preprints/lectures-pcmi.pdf)
- [Ang2025] David Kurniadi Angdinata. "L-functions of Dirichlet twists of elliptic curves:
  computations and congruences." PhD thesis, University College London (2025),
  [discovery.ucl.ac.uk](https://discovery.ucl.ac.uk/10223687/1/main-pages.pdf)
- [Ada] Tom Adamczewski. "Autoformalized conjectures",
  [Birch and Swinnerton-Dyer](https://tadamcz.com/autoformalization-results/#/p/wp-birch-and-swinnerton-dyer-conjecture)

`WeierstrassCurve.LSeries` is Mathlib's Euler product: `LFunction` multiplies the local factors
`localEulerFactor`, read off a minimal model over each `p`-adic completion.
`weak_iff_analyticOrder` shows that, once an entire continuation of this series exists, `Weak ℚ`
is the equality of its analytic order at $s = 1$ with `AddCommGroup.freeRank`. Wiles' account of
the Clay problem is this equality for the product over primes of good reduction. That product and
`E.LSeries` differ by the Euler factors at primes of bad reduction, which are holomorphic and
non-zero at $s = 1$. The comparison of those two products is left unformalised.
-/

@[expose] public section

namespace BSD

open HasseWeil

/-- The **weak Birch and Swinnerton-Dyer conjecture** for a number field $K$: for every elliptic
curve $E$ over $K$, a meromorphic continuation of its $L$-series has order
$\operatorname{rank}_{\mathbb{Z}} E(K)$ at $s = 1$. [Gross2011], Conjecture 2.10 states the
conjecture assuming only a meromorphic continuation near $s = 1$, while
`HasseWeil.HasMeromorphicContinuation` asks for one on all of $\mathbb{C}$.

The rank is `AddCommGroup.freeRank`, which requires $E(K)$ to be finitely generated. That is the
Mordell--Weil theorem, which Mathlib does not have and which this repository states as a `sorry`
in `EllipticCurveRank.mordell_weil`, so it appears here as a hypothesis. -/
def Weak (K : Type*) [Field K] [NumberField K] [DecidableEq K] : Prop :=
  ∀ (E : WeierstrassCurve K) [E.IsElliptic] [AddGroup.FG E.toAffine.Point] (L : ℂ → ℂ),
    HasMeromorphicContinuation E L →
      meromorphicOrderAt L 1 = AddCommGroup.freeRank E.toAffine.Point

/-- **Weak Birch and Swinnerton-Dyer conjecture** ([Tate1966], Conjecture (A)). -/
@[category research open, AMS 11 14]
theorem weak_birch_swinnerton_dyer_conjecture (K : Type*) [Field K] [NumberField K]
    [DecidableEq K] : Weak K := by
  sorry

/-- The **weak Birch and Swinnerton-Dyer conjecture** over $\mathbb{Q}$, a Clay Millennium Prize
Problem. Once every elliptic curve over $\mathbb{Q}$ has an entire continuation of its $L$-series,
`weak_iff_analyticOrder` identifies this with the analytic-order formulation below. -/
@[category research open, AMS 11 14]
theorem weak_birch_swinnerton_dyer_conjecture_rat : Weak ℚ := by
  sorry

/-! ## Analytic order over $\mathbb{Q}$

Wiles states the Clay problem as follows. The $L$-series of an elliptic curve $E$ over
$\mathbb{Q}$ extends to an entire function, and the Taylor expansion of that function at $s = 1$
is $c(s - 1)^r$ plus higher-order terms, with $c \neq 0$ and $r = \operatorname{rank} E(\mathbb{Q})$.
The entire continuation is the modularity theorem, recorded as
`HasseWeil.exists_hasAnalyticContinuation_rat`. The series itself is `E.LSeries`. -/

section AnalyticOrder

open scoped Topology

variable {E : WeierstrassCurve ℚ}

/-- Two entire continuations of `E.LSeries` agree on $\mathbb{C}$. -/
@[category API, AMS 11 14]
theorem analyticContinuation_eq {L L' : ℂ → ℂ} (hL : HasAnalyticContinuation E L)
    (hL' : HasAnalyticContinuation E L') : L = L' := by
  apply AnalyticOnNhd.eq_of_frequently_eq (z₀ := 2) (fun z _ ↦ hL.1 z) (fun z _ ↦ hL'.1 z)
  refine (Filter.eventually_of_mem (nhdsWithin_le_nhds <|
      (Complex.isOpen_re_gt (3 / 2)).mem_nhds (x := 2) (by norm_num)) fun s hs ↦
    (hL.2 s hs).trans (hL'.2 s hs).symm).frequently

/-- Where `f` is analytic, its analytic order at `z` is the natural number `r` if and only if its
meromorphic order at `z` is `r`. -/
@[category API, AMS 11 14]
theorem analyticOrderAt_eq_nat_iff_meromorphicOrderAt {f : ℂ → ℂ} {z : ℂ} {r : ℕ}
    (hf : AnalyticAt ℂ f z) : analyticOrderAt f z = r ↔ meromorphicOrderAt f z = r := by
  rw [hf.meromorphicOrderAt_eq]
  constructor
  · intro h
    rw [h]
    simp
  · intro h
    cases hord : analyticOrderAt f z with
    | top =>
      rw [hord, ENat.map_top] at h
      exact (WithTop.top_ne_natCast (α := ℤ) r h).elim
    | coe n =>
      simp only [ENat.map_natCast] at h
      norm_cast at h
      simpa [hord] using h

variable [AddGroup.FG E.toAffine.Point]

/-- Suppose the group of rational points of `E` is finitely generated and `E.LSeries` has an entire
continuation. The analytic order of that continuation at $s = 1$ equals `AddCommGroup.freeRank`
if and only if every meromorphic continuation has that same meromorphic order. -/
@[category API, AMS 11 14]
theorem meromorphicOrder_eq_freeRank_iff_analyticOrder
    (hAn : ∃ L, HasAnalyticContinuation E L) :
    (∃ L, HasAnalyticContinuation E L ∧
        analyticOrderAt L 1 = AddCommGroup.freeRank E.toAffine.Point) ↔
      ∀ L, HasMeromorphicContinuation E L →
        meromorphicOrderAt L 1 = AddCommGroup.freeRank E.toAffine.Point := by
  obtain ⟨L₀, hL₀⟩ := hAn
  constructor
  · rintro ⟨L, hL, hr⟩ M hM
    have hagree : L =ᶠ[𝓝[≠] 1] M :=
      hL.hasMeromorphicContinuation.unique hM 1
    rw [← meromorphicOrderAt_congr hagree]
    exact (analyticOrderAt_eq_nat_iff_meromorphicOrderAt (hL.1 1)).1 hr
  · intro hMer
    refine ⟨L₀, hL₀, (analyticOrderAt_eq_nat_iff_meromorphicOrderAt (hL₀.1 1)).2 ?_⟩
    exact hMer L₀ hL₀.hasMeromorphicContinuation

end AnalyticOrder

/-- Assume every elliptic curve over $\mathbb{Q}$ has an entire continuation of `E.LSeries`.
Then `Weak ℚ` holds if and only if, for every such curve with finitely generated Mordell--Weil
group, that continuation has analytic order `AddCommGroup.freeRank` at $s = 1$.

This is Wiles' formulation of the Clay problem, expressed with `WeierstrassCurve.LSeries`.
The hypothesis is `HasseWeil.exists_hasAnalyticContinuation_rat`. Finite generation is
`EllipticCurveRank.mordell_weil`. -/
@[category API, AMS 11 14]
theorem weak_iff_analyticOrder
    (hAn : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], ∃ L, HasAnalyticContinuation E L) :
    Weak ℚ ↔ ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] [AddGroup.FG E.toAffine.Point],
      ∃ L, HasAnalyticContinuation E L ∧
        analyticOrderAt L 1 = AddCommGroup.freeRank E.toAffine.Point := by
  constructor
  · intro hW E _ _
    exact (meromorphicOrder_eq_freeRank_iff_analyticOrder (hAn E)).2 fun L hL ↦ hW E L hL
  · intro hClay E _ _ L hL
    exact (meromorphicOrder_eq_freeRank_iff_analyticOrder (hAn E)).1 (hClay E) L hL

end BSD
