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

## References

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
  [annals](https://annals.math.princeton.edu/wp-content/uploads/annals-v172-n1-p11-p.pdf)
-/

namespace WeierstrassCurve.Affine

open Projective HasseWeil NumberField

/-- **Mordell--Weil theorem**: the rational points of an elliptic curve over a number field form
a finitely generated group. See [Silverman2009], Theorem VIII.6.7. -/
@[instance, category textbook, AMS 11 14]
theorem Point.fg {K : Type*} [Field K] [NumberField K] [DecidableEq K] (E : Affine K)
    [E.IsElliptic] : AddGroup.FG E.Point := by
  sorry

namespace NumberField

/-- The **weak Birch and Swinnerton-Dyer conjecture** for a number field `K`: for every elliptic
curve `E` over `K`, the L-series of `E` has a meromorphic continuation whose order at `s = 1` is
`rk E(K)`. Following [DD2010], Conjecture 2.1 (1), the continuation is asserted rather than assumed,
so this implies `HasseWeil.exists_hasMeromorphicContinuation`. [Tate1966], Conjecture (A) and
[Gross2011], Conjecture 2.10 instead take a continuation as given and state only the order, and
[Gross2011] needs one only near `s = 1`. By `HasseWeil.HasMeromorphicContinuation.unique` the order
does not depend on which continuation is taken, so the two readings differ exactly by the
Hasse--Weil conjecture. -/
def WeakBSD {K : Type*} [Field K] [NumberField K] [DecidableEq K] (E : Affine K) : Prop :=
  ∃ L : ℂ → ℂ, HasMeromorphicContinuation E L ∧ meromorphicOrderAt L 1 = Module.finrank ℤ E.Point

/-- The leading coefficient predicted by BSD over a number field, using the non-normalised regulator
and dividing by the square root of the absolute field discriminant. -/
noncomputable def leadingCoefficient {K : Type*} [Field K] [NumberField K] [DecidableEq K]
    (E : Affine K) [E.IsElliptic] : ℝ :=
  E.period * Point.regulator E * Nat.card E.tateShafarevich * E.toProjective.tamagawaProduct /
      (|(discr K : ℝ)|.sqrt * (Nat.card <| AddCommGroup.torsion E.Point) ^ 2 : ℝ)

/-- The **strong Birch and Swinnerton-Dyer conjecture** over a number field `K`: for every elliptic
curve `E` over `K`, a meromorphic continuation of its L-series has order `rk E(K)` at `s = 1`, the
Tate--Shafarevich group is finite, and the leading coefficient of its L-series is
`L⁽ʳ⁾(E, 1) / r! = Ω(E)·Reg(E)·|Sha(E)|·∏ᵥcᵥ / √|Δ(K)|·|E(K)ₜₒᵣₛ|²`. See [DD2010], Conjecture 2.1. -/
def StrongBSD {K : Type*} [Field K] [NumberField K] [DecidableEq K] (E : Affine K) [E.IsElliptic] :
    Prop := ∃ L : ℂ → ℂ,
  HasMeromorphicContinuation E L ∧ meromorphicOrderAt L 1 = Module.finrank ℤ E.Point ∧
    Finite E.tateShafarevich ∧ meromorphicTrailingCoeffAt L 1 = leadingCoefficient E

/-- The **weak Birch and Swinnerton-Dyer conjecture** ([DD2010], Conjecture 2.1 (1); the order
statement on its own is [Tate1966], Conjecture (A)). -/
@[category research open, AMS 11 14]
theorem weak_birch_swinnerton_dyer {K : Type*} [Field K] [NumberField K] [DecidableEq K]
    (E : Affine K) [E.IsElliptic] : WeakBSD E := by
  sorry

/-- The **strong Birch and Swinnerton-Dyer conjecture** ([DD2010], Conjecture 2.1). -/
@[category research open, AMS 11 14]
theorem strong_birch_swinnerton_dyer {K : Type*} [Field K] [NumberField K]
    [DecidableEq K] (E : Affine K) [E.IsElliptic] : StrongBSD E := by
  sorry

/-- Strong BSD implies weak BSD, since the meromorphic continuation witnessing the strong conjecture
already has the predicted order at `s = 1`. -/
@[category API, AMS 11 14]
theorem StrongBSD.weakBSD {K : Type*} [Field K] [NumberField K] [DecidableEq K] {E : Affine K}
    [E.IsElliptic] (h : StrongBSD E) : WeakBSD E :=
  ⟨h.choose, h.choose_spec.left, h.choose_spec.right.left⟩

end NumberField

namespace Rat

/-- The **weak Birch and Swinnerton-Dyer conjecture** over `ℚ`, a Clay Millennium Prize Problem. -/
@[category research open, AMS 11 14]
theorem weak_birch_swinnerton_dyer (E : Affine ℚ) [E.IsElliptic] :
    NumberField.WeakBSD E := by
  sorry

/-- The **strong Birch and Swinnerton-Dyer conjecture** over `ℚ`. -/
@[category research open, AMS 11 14]
theorem strong_birch_swinnerton_dyer (E : Affine ℚ) [E.IsElliptic] :
    NumberField.StrongBSD E := by
  sorry

end Rat

end WeierstrassCurve.Affine
