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
import FormalConjectures.Wikipedia.HasseWeil

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
- [Silverman2009] Joseph H. Silverman. *The Arithmetic of Elliptic Curves*. 2nd ed., Graduate Texts
  in Mathematics 106, Springer (2009), [doi](https://doi.org/10.1007/978-0-387-09494-6)
- [DD2010] Tim Dokchitser and Vladimir Dokchitser. "On the Birch-Swinnerton-Dyer quotients
  modulo squares." Annals of Mathematics 172 (2010), 567-596, Conjecture 2.1,
  [PDF](https://annals.math.princeton.edu/wp-content/uploads/annals-v172-n1-p11-p.pdf)
-/

namespace WeierstrassCurve

/-- **Mordell--Weil theorem**: the rational points of an elliptic curve over a number field form
a finitely generated group. See [Silverman2009], Theorem VIII.6.7. -/
@[instance, category textbook, AMS 11 14]
theorem Affine.Point.fg {K : Type*} [Field K] [NumberField K] [DecidableEq K] (E : Affine K)
    [E.IsElliptic] : AddGroup.FG E.Point := by
  sorry

end WeierstrassCurve

namespace BSD

open HasseWeil

/-- The **weak Birch and Swinnerton-Dyer conjecture** for a number field $K$: for every elliptic
curve $E$ over $K$, a meromorphic continuation of its $L$-series has order
$\operatorname{rank}_{\mathbb{Z}} E(K)$ at $s = 1$. [Gross2011], Conjecture 2.10 states the
conjecture assuming only a meromorphic continuation near $s = 1$, while
`HasseWeil.HasMeromorphicContinuation` asks for one on all of $\mathbb{C}$.

The rank is `Module.finrank ℤ E.toAffine.Point`. Finite generation follows from the
Mordell--Weil theorem `WeierstrassCurve.Affine.Point.fg`. -/
def Weak (K : Type*) [Field K] [NumberField K] [DecidableEq K] : Prop :=
  ∀ (E : WeierstrassCurve K) [E.IsElliptic] (L : ℂ → ℂ),
    HasMeromorphicContinuation E L → meromorphicOrderAt L 1 = Module.finrank ℤ E.toAffine.Point

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

section Strong

variable {K : Type*} [Field K] [NumberField K] [DecidableEq K]

/-- The leading coefficient predicted by BSD over a number field, using the non-normalised
regulator and dividing by the square root of the absolute field discriminant. The period is
`WeierstrassCurve.period`, whose full real periods include the real component factors, so the
Tamagawa product uses only finite places. -/
noncomputable def arithmeticLeadingCoefficient (E : WeierstrassCurve K) [E.IsElliptic] : ℝ :=
  E.period * WeierstrassCurve.Affine.Point.regulator E.toAffine *
    Nat.card E.toAffine.tateShafarevich * E.toProjective.tamagawaProduct /
      (Real.sqrt |(NumberField.discr K : ℝ)| *
        (Nat.card (AddCommGroup.torsion E.toAffine.Point) : ℝ) ^ 2)

/-- The **strong Birch and Swinnerton-Dyer conjecture** over a number field $K$: the
Tate--Shafarevich group is finite, and a meromorphic continuation of the $L$-series has order
$r=\operatorname{rank}_{\mathbb{Z}} E(K)$ at $1$, with leading coefficient
$\Omega(E)\operatorname{Reg}(E/K)|\Sha(E/K)|\prod_v c_v /
(\sqrt{|\operatorname{disc}K|}\,|E(K)_{\mathrm{tors}}|^2)$.

The leading coefficient is the coefficient of $(s-1)^r$, equivalently $L^{(r)}(E/K,1)/r!$.
The product is over finite places and the period includes the minimal-discriminant correction.
See [DD2010], Conjecture 2.1. -/
def Strong (K : Type*) [Field K] [NumberField K] [DecidableEq K] : Prop :=
  ∀ (E : WeierstrassCurve K) [E.IsElliptic],
    Finite E.toAffine.tateShafarevich ∧ ∃ L : ℂ → ℂ, HasMeromorphicContinuation E L ∧
      meromorphicOrderAt L 1 = Module.finrank ℤ E.toAffine.Point ∧
      meromorphicTrailingCoeffAt L 1 = (arithmeticLeadingCoefficient E : ℂ)

/-- Strong BSD implies weak BSD, since two meromorphic continuations agree near $1$ and so have the
same order there. -/
@[category API, AMS 11 14]
theorem Strong.weak (h : Strong K) : Weak K := by
  intro E hE L hL
  obtain ⟨_, L', hL', hr, _⟩ := h E
  exact (meromorphicOrderAt_congr (hL.unique hL' 1)).trans hr

/-- **Strong Birch and Swinnerton-Dyer conjecture** over a number field, including finiteness of the
Tate--Shafarevich group and the leading-coefficient formula ([DD2010], Conjecture 2.1). -/
@[category research open, AMS 11 14]
theorem strong_birch_swinnerton_dyer_conjecture (K : Type*) [Field K] [NumberField K]
    [DecidableEq K] : Strong K := by
  sorry

/-- The **strong Birch and Swinnerton-Dyer conjecture** over $\mathbb{Q}$. -/
@[category research open, AMS 11 14]
theorem strong_birch_swinnerton_dyer_conjecture_rat : Strong ℚ := by
  sorry

end Strong

end BSD
