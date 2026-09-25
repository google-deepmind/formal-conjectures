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
Problem. -/
@[category research open, AMS 11 14]
theorem weak_birch_swinnerton_dyer_conjecture_rat : Weak ℚ := by
  sorry

/-! ## An explicit Euler-product variant over $\mathbb{Q}$

The statement below does not refer to `WeierstrassCurve.LSeries`. It builds $L(E, s)$ directly
from its Euler product
$$L(E, s) = \prod_p \left(1 - a_p p^{-s} + \mathbb{1}_{\text{good}}(p)\, p^{1-2s}\right)^{-1},$$
valid for $\operatorname{Re} s > 3/2$, where $a_p = p - \#\{(x, y) \in \mathbb{F}_p^2\}$ counts the
affine points of the reduction of a $p$-minimal model of $E$. This uniform formula gives the usual
values $a_p = 1, -1, 0$ at split multiplicative, non-split multiplicative and additive reduction
respectively. -/

section EulerProduct

open WeierstrassCurve

/-- `W` is an integral model of `E`: a Weierstrass curve over $\mathbb{Z}$ whose base change to
$\mathbb{Q}$ is obtained from `E` by an admissible change of variables. -/
def IsIntegralModel (E : WeierstrassCurve ℚ) (W : WeierstrassCurve ℤ) : Prop :=
  ∃ C : VariableChange ℚ, C • E = W.map (Int.castRingHom ℚ)

/-- `W` is a model of `E` that is minimal at `p`: an integral model whose discriminant has the
least possible $p$-adic valuation among all integral models. -/
def IsMinimalModelAt (E : WeierstrassCurve ℚ) (p : ℕ) (W : WeierstrassCurve ℤ) : Prop :=
  IsIntegralModel E W ∧ ∀ W' : WeierstrassCurve ℤ, IsIntegralModel E W' →
    padicValInt p W.Δ ≤ padicValInt p W'.Δ

/-- A chosen model of `E` that is minimal at `p` (one exists, see `exists_isMinimalModelAt`). -/
noncomputable def minimalModelAt (E : WeierstrassCurve ℚ) (p : ℕ) : WeierstrassCurve ℤ :=
  Classical.epsilon (IsMinimalModelAt E p)

/-- The number of affine $\mathbb{F}_p$-points of the reduction mod $p$ of an integral
Weierstrass curve (singular points included). -/
noncomputable def affineCountModP (W : WeierstrassCurve ℤ) (p : ℕ) : ℕ :=
  Nat.card {xy : ZMod p × ZMod p //
    (W.map (Int.castRingHom (ZMod p))).toAffine.Equation xy.1 xy.2}

/-- The trace of Frobenius $a_p(E) = p + 1 - \#\tilde{E}(\mathbb{F}_p)$, i.e. $p$ minus the number
of affine points of $\tilde{E}$ over $\mathbb{F}_p$. -/
noncomputable def ap (E : WeierstrassCurve ℚ) (p : ℕ) : ℤ :=
  (p : ℤ) - affineCountModP (minimalModelAt E p) p

/-- `E` has good reduction at `p`: $p$ does not divide the discriminant of a $p$-minimal model. -/
def HasGoodReductionAt (E : WeierstrassCurve ℚ) (p : ℕ) : Prop :=
  ¬ (p : ℤ) ∣ (minimalModelAt E p).Δ

open Classical in
/-- The local Euler factor of $L(E, s)$ at $p$. -/
noncomputable def localFactor (E : WeierstrassCurve ℚ) (p : ℕ) (s : ℂ) : ℂ :=
  (1 - (ap E p : ℂ) * (p : ℂ) ^ (-s)
    + (if HasGoodReductionAt E p then (p : ℂ) ^ (1 - 2 * s) else 0))⁻¹

/-- The Euler product defining $L(E, s)$ (absolutely convergent for $\operatorname{Re} s > 3/2$). -/
noncomputable def eulerProduct (E : WeierstrassCurve ℚ) (s : ℂ) : ℂ :=
  ∏' p : Nat.Primes, localFactor E p s

/-- Every rational Weierstrass curve has an integral model (clear denominators by scaling). -/
@[category API, AMS 11 14]
theorem exists_isIntegralModel (E : WeierstrassCurve ℚ) :
    ∃ W : WeierstrassCurve ℤ, IsIntegralModel E W := by
  have aux : ∀ (q : ℚ) (n : ℕ) (m : ℤ), (q.den : ℤ) ∣ m → 1 ≤ n →
      ∃ z : ℤ, (z : ℚ) = (m : ℚ) ^ n * q := by
    intro q n m h hn
    obtain ⟨k, rfl⟩ := h
    refine ⟨q.num * k * (q.den * k) ^ (n - 1), ?_⟩
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
    rw [← Rat.mul_den_eq_num]
    ring
  set D : ℤ := E.a₁.den * E.a₂.den * E.a₃.den * E.a₄.den * E.a₆.den with hD
  have hD0 : (D : ℚ) ≠ 0 := by simp [hD]
  obtain ⟨z1, h1⟩ := aux E.a₁ 1 D
    ⟨E.a₂.den * E.a₃.den * E.a₄.den * E.a₆.den, by rw [hD]; ring⟩ le_rfl
  obtain ⟨z2, h2⟩ := aux E.a₂ 2 D
    ⟨E.a₁.den * E.a₃.den * E.a₄.den * E.a₆.den, by rw [hD]; ring⟩ (by norm_num)
  obtain ⟨z3, h3⟩ := aux E.a₃ 3 D
    ⟨E.a₁.den * E.a₂.den * E.a₄.den * E.a₆.den, by rw [hD]; ring⟩ (by norm_num)
  obtain ⟨z4, h4⟩ := aux E.a₄ 4 D
    ⟨E.a₁.den * E.a₂.den * E.a₃.den * E.a₆.den, by rw [hD]; ring⟩ (by norm_num)
  obtain ⟨z6, h6⟩ := aux E.a₆ 6 D
    ⟨E.a₁.den * E.a₂.den * E.a₃.den * E.a₄.den, by rw [hD]; ring⟩ (by norm_num)
  refine ⟨⟨z1, z2, z3, z4, z6⟩,
    ⟨Units.mk0 ((D : ℚ)⁻¹) (inv_ne_zero hD0), 0, 0, 0⟩, ?_⟩
  ext <;> simp [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, h1, h2, h3, h4, h6]

/-- Models minimal at `p` exist, so `minimalModelAt` is a genuine minimal model. -/
@[category API, AMS 11 14]
theorem exists_isMinimalModelAt (E : WeierstrassCurve ℚ) (p : ℕ) :
    ∃ W : WeierstrassCurve ℤ, IsMinimalModelAt E p W := by
  classical
  have hex : ∃ n : ℕ, ∃ W, IsIntegralModel E W ∧ padicValInt p W.Δ = n := by
    obtain ⟨W, hW⟩ := exists_isIntegralModel E
    exact ⟨_, W, hW, rfl⟩
  obtain ⟨W, hW, hWn⟩ := Nat.find_spec hex
  refine ⟨W, hW, fun W' hW' => ?_⟩
  rw [hWn]
  exact Nat.find_min' hex ⟨W', hW', rfl⟩

/-- **Weak Birch and Swinnerton-Dyer conjecture** over $\mathbb{Q}$, Euler-product form
([Tate1966], Conjecture (A)). The Euler product $L(E, s)$ extends to an entire function `L`,
whose order of vanishing at $s = 1$ is a natural number $r$ equal to the rank of $E(\mathbb{Q})$.
Such an entire extension is unique by the identity theorem, and it exists by the modularity
theorem, so the content is the equality of the analytic and algebraic ranks.

Unlike `weak_birch_swinnerton_dyer_conjecture_rat`, the rank is `Module.rank`, so no
Mordell--Weil hypothesis is needed: the statement also asserts that this rank is finite. -/
@[category research open, AMS 11 14]
theorem weak_birch_swinnerton_dyer_conjecture_rat_eulerProduct (E : WeierstrassCurve ℚ)
    [E.IsElliptic] :
    ∃ L : ℂ → ℂ, Differentiable ℂ L ∧
      (∀ s : ℂ, 3 / 2 < s.re → L s = eulerProduct E s) ∧
      ∃ r : ℕ, analyticOrderAt L 1 = r ∧ Module.rank ℤ E.toAffine.Point = r := by
  sorry

end EulerProduct

end BSD
