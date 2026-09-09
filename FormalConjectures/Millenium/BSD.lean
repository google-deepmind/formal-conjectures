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

import FormalConjecturesUtil

/-!
# The Birch and Swinnerton-Dyer (BSD) Conjecture

*References:*
- [The Clay Institute](https://www.claymath.org/millennium/birch-and-swinnerton-dyer-conjecture/),
  official problem description by Andrew Wiles:
  [PDF](https://www.claymath.org/wp-content/uploads/2022/05/birchswin.pdf)
- [BSD1965] B. J. Birch and H. P. F. Swinnerton-Dyer. "Notes on elliptic curves. II."
  Journal fur die reine und angewandte Mathematik 218 (1965), 79-108,
  [doi](https://doi.org/10.1515/crll.1965.218.79)
- [Tate1966] John Tate. "On the conjectures of Birch and Swinnerton-Dyer and a geometric analog."
  Seminaire Bourbaki, Vol. 9, Exp. No. 306 (1966), 415-440,
  [numdam](https://www.numdam.org/item/SB_1964-1966__9__415_0/)
- [Gross2011] Benedict H. Gross. "Lectures on the conjecture of Birch and Swinnerton-Dyer."
  Arithmetic of L-functions, IAS/Park City Math. Ser. 18, AMS (2011), 169-209,
  [PDF](https://people.math.harvard.edu/~gross/preprints/lectures-pcmi.pdf)
- [Ang2025] David Kurniadi Angdinata. "L-functions of Dirichlet twists of elliptic curves:
  computations and congruences." PhD thesis, University College London (2025),
  [PDF](https://discovery.ucl.ac.uk/10223687/1/main-pages.pdf)
- [Ada] Tom Adamczewski. "Autoformalized conjectures",
  [Birch and Swinnerton-Dyer](https://tadamcz.com/autoformalization-results/#/p/wp-birch-and-swinnerton-dyer-conjecture)
-/

namespace BirchSwinnertonDyer

open scoped Topology

section NumberField

variable {K : Type*} [Field K] [NumberField K] {E : WeierstrassCurve K}

def IsLFunction (E : WeierstrassCurve K) (L : ℂ → ℂ) : Prop :=
  Meromorphic L ∧ ∀ s : ℂ, 3 / 2 < s.re → L s = E.LSeries s

@[category API, AMS 11 14]
theorem IsLFunction.unique {L L' : ℂ → ℂ} (hL : IsLFunction E L) (hL' : IsLFunction E L')
    (x : ℂ) : L =ᶠ[𝓝[≠] x] L' := by
  have h2 : meromorphicOrderAt (L - L') 2 = ⊤ := meromorphicOrderAt_eq_top_iff.2 <|
    Filter.Eventually.mono (nhdsWithin_le_nhds <| (Complex.isOpen_re_gt (3 / 2)).mem_nhds
      (by norm_num)) fun s hs => sub_eq_zero.2 ((hL.2 s hs).trans (hL'.2 s hs).symm)
  have key : meromorphicOrderAt (L - L') x = ⊤ := not_not.1 fun hx =>
    (hL.1.sub hL'.1).exists_meromorphicOrderAt_ne_top_iff_forall.1 ⟨x, hx⟩ 2 h2
  exact (meromorphicOrderAt_eq_top_iff.1 key).mono fun s hs => sub_eq_zero.1 hs

/-- **Hasse--Weil conjecture**: the $L$-function of an elliptic curve over a number field extends
to the whole plane. -/
@[category research open, AMS 11 14]
theorem exists_isLFunction (E : WeierstrassCurve K) [E.IsElliptic] : ∃ L, IsLFunction E L := by
  sorry

end NumberField

section Rat

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- The **Hasse--Weil conjecture** over $\mathbb{Q}$, a consequence of the modularity theorem. -/
@[category research solved, AMS 11 14]
theorem exists_isLFunction_rat : ∃ L, IsLFunction E L := by
  sorry

end Rat

/-- The **weak Birch and Swinnerton-Dyer conjecture** for a number field $K$: for every elliptic
curve $E$ over $K$, a meromorphic continuation of its $L$-series has order
$\operatorname{rank}_{\mathbb{Z}} E(K)$ at $s = 1$.

The rank is `AddCommGroup.freeRank`, which requires $E(K)$ to be finitely generated. That is the
Mordell--Weil theorem, which Mathlib does not have and which this repository states as a `sorry`
in `EllipticCurveRank.mordell_weil`, so it appears here as a hypothesis. -/
def Weak (K : Type*) [Field K] [NumberField K] [DecidableEq K] : Prop :=
  ∀ (E : WeierstrassCurve K) [E.IsElliptic] [AddGroup.FG E.toAffine.Point] (L : ℂ → ℂ),
    IsLFunction E L → meromorphicOrderAt L 1 = AddCommGroup.freeRank E.toAffine.Point

/-- **Weak Birch and Swinnerton-Dyer conjecture** ([Tate1966], Conjecture (A)). -/
@[category research open, AMS 11 14]
theorem weak_birch_swinnerton_dyer_conjecture (K : Type*) [Field K] [NumberField K]
    [DecidableEq K] : Weak K := by
  sorry

/-- The **weak Birch and Swinnerton-Dyer conjecture** over $\mathbb{Q}$, a Clay Millennium Prize
Problem. -/
@[category research open, AMS 11 14]
theorem weak_birch_swinnerton_dyer_conjecture_rat : Weak ℚ := by
  sorry

end BirchSwinnertonDyer
