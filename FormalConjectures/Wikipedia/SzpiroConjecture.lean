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

/-!
# Szpiro's conjecture and the modified Szpiro conjecture

Proposed by Lucien Szpiro around 1981, **Szpiro's conjecture** bounds the minimal discriminant
$\Delta$ of an elliptic curve $E / \mathbb{Q}$ by a power of its arithmetic conductor $f$: for
every $\varepsilon > 0$, there exists $C(\varepsilon) > 0$ such that $|\Delta| \le C(\varepsilon)
f^{6 + \varepsilon}$. The **modified Szpiro conjecture**, which bounds $\max\{|c_4|^3, |c_6|^2\}
\le C(\varepsilon) f^{6 + \varepsilon}$ on a global minimal integral model, is equivalent to the
Oesterlé–Masser $abc$ conjecture (see `FormalConjectures.Wikipedia.ABC`).

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Szpiro%27s_conjecture)
- [Sz90] L. Szpiro, *Discriminant et conducteur des courbes elliptiques*, Astérisque 183 (1990),
  7–18.
- [Oe88] J. Oesterlé, *Nouvelles approches du "théorème" de Fermat*, Séminaire Bourbaki, Exp. 694,
  Astérisque 161–162 (1988), 165–186.
- [Si94] J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Graduate Texts in
  Mathematics 151, Springer, 1994, Theorem IV.10.4.
- [Si09] J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts in
  Mathematics 106, Springer, 2009, Section VIII.8.
-/

@[expose] public section

namespace SzpiroConjecture

/-- An integral Weierstrass curve $W$ over $\mathbb{Z}$ is a *global minimal model* of an elliptic
curve over $\mathbb{Q}$ if $\Delta(W) \ne 0$ and $|\Delta(W)|$ is minimal among all integral
Weierstrass models $\mathbb{Q}$-isomorphic to $W$ via `WeierstrassCurve.VariableChange ℚ`. Every
elliptic curve over $\mathbb{Q}$ admits such a model because $\mathbb{Z}$ has class number $1$
([Si09], Corollary VIII.8.3). -/
def IsGlobalMinimalModel (W : WeierstrassCurve ℤ) : Prop :=
  W.Δ ≠ 0 ∧ ∀ (W' : WeierstrassCurve ℤ) (C : WeierstrassCurve.VariableChange ℚ),
    C • W.map (algebraMap ℤ ℚ) = W'.map (algebraMap ℤ ℚ) → W.Δ.natAbs ≤ W'.Δ.natAbs

/-- The tame conductor $\prod_{p \mid |\Delta|} p \cdot \prod_{p \mid \gcd(c_4, \Delta)} p$ of a
global minimal Weierstrass model $W$ over $\mathbb{Z}$. At every prime $p \ge 5$, this has exact
conductor valuation ($0$ at good reduction, $1$ at multiplicative reduction, and $2$ at additive
reduction); at $p \in \{2, 3\}$, wild ramification increases the arithmetic conductor $f$ by a
factor dividing $2^6 \cdot 3^3 = 1728$ ([Si94], Theorem IV.10.4). -/
def tameConductor (W : WeierstrassCurve ℤ) : ℕ :=
  (∏ p ∈ W.Δ.natAbs.primeFactors, p) * (∏ p ∈ (Int.gcd W.c₄ W.Δ).primeFactors, p)

/-- Every global minimal integral Weierstrass model has positive absolute discriminant. -/
@[category API, AMS 11 14]
theorem isGlobalMinimalModel_natAbs_pos {W : WeierstrassCurve ℤ} (hW : IsGlobalMinimalModel W) :
    1 ≤ W.Δ.natAbs :=
  Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hW.1)

/-- When $\gcd(c_4(W), \Delta(W)) = 1$ (semistable case), `tameConductor W` equals the radical of
$|\Delta(W)|$. -/
@[category API, AMS 11 14]
theorem tameConductor_eq_prod_primeFactors_of_coprime (W : WeierstrassCurve ℤ)
    (hcop : Int.gcd W.c₄ W.Δ = 1) :
    tameConductor W = ∏ p ∈ W.Δ.natAbs.primeFactors, p := by
  simp [tameConductor, hcop]

/-- On the modular curve $X_0(11)$ with minimal equation $y^2 + y = x^3 - x^2$, the discriminant is
$\Delta = -11$. -/
@[category test, AMS 11 14]
theorem x0_eleven_discriminant :
    (⟨0, -1, 1, 0, 0⟩ : WeierstrassCurve ℤ).Δ = -11 := by
  norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- On the modular curve $X_0(11)$ ($y^2 + y = x^3 - x^2$), `tameConductor` evaluates to $11$. -/
@[category test, AMS 11 14]
theorem x0_eleven_tameConductor :
    tameConductor ⟨0, -1, 1, 0, 0⟩ = 11 := by
  let W : WeierstrassCurve ℤ := ⟨0, -1, 1, 0, 0⟩
  have hΔ : W.Δ = -11 := x0_eleven_discriminant
  have hc4 : W.c₄ = 16 := by
    norm_num [W, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  have hgcd : Int.gcd W.c₄ W.Δ = 1 := by
    rw [hc4, hΔ]
    decide
  rw [tameConductor_eq_prod_primeFactors_of_coprime W hgcd, hΔ]
  change (∏ p ∈ (11 : ℕ).primeFactors, p) = 11
  rw [Nat.Prime.primeFactors (by decide), Finset.prod_singleton]

/-- **Szpiro's Conjecture** ([Sz90]): For every $\varepsilon > 0$, there exists $C > 0$ such that
every global minimal integral Weierstrass model $W$ of an elliptic curve over $\mathbb{Q}$ satisfies
$$|\Delta(W)| \le C \cdot f_W^{6 + \varepsilon}.$$

Note: Because Mathlib does not yet define Tate's wild conductor exponents at $p \in \{2, 3\}$, we
state the bound using $f_{\mathrm{tame}}(W) =$ `tameConductor W`. Since the exact conductor $f$
satisfies $f_{\mathrm{tame}}(W) \le f \le 1728\, f_{\mathrm{tame}}(W)$ on every global minimal
model, the resulting inequality matches the exact-conductor formulation up to rescaling $C$ by
$1728^{6 + \varepsilon}$. -/
@[category research open, AMS 11 14]
theorem szpiro_conjecture (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ W : WeierstrassCurve ℤ,
        IsGlobalMinimalModel W →
          (W.Δ.natAbs : ℝ) ≤ C * (tameConductor W : ℝ) ^ (6 + ε) := by
  sorry

/-- **Modified Szpiro Conjecture** ([Oe88]): For every $\varepsilon > 0$, there exists $C > 0$ such
that every global minimal integral Weierstrass model $W$ of an elliptic curve over $\mathbb{Q}$
satisfies
$$\max\{|c_4(W)|^3, |c_6(W)|^2\} \le C \cdot f_W^{6 + \varepsilon},$$
stated with `tameConductor W` (equivalent to the exact arithmetic conductor up to a bounded factor
dividing $1728$). -/
@[category research open, AMS 11 14]
theorem modified_szpiro_conjecture (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ W : WeierstrassCurve ℤ,
        IsGlobalMinimalModel W →
          max ((W.c₄.natAbs : ℝ) ^ 3) ((W.c₆.natAbs : ℝ) ^ 2) ≤
            C * (tameConductor W : ℝ) ^ (6 + ε) := by
  sorry

/-- Since $1728 \Delta = c_4^3 - c_6^2$, the modified Szpiro conjecture implies Szpiro's
conjecture. -/
@[category API, AMS 11 14]
theorem szpiro_of_modified_szpiro (ε : ℝ)
    (hmod : ∃ C : ℝ, 0 < C ∧ ∀ W : WeierstrassCurve ℤ, IsGlobalMinimalModel W →
      max ((W.c₄.natAbs : ℝ) ^ 3) ((W.c₆.natAbs : ℝ) ^ 2) ≤
        C * (tameConductor W : ℝ) ^ (6 + ε)) :
    ∃ C : ℝ, 0 < C ∧ ∀ W : WeierstrassCurve ℤ, IsGlobalMinimalModel W →
      (W.Δ.natAbs : ℝ) ≤ C * (tameConductor W : ℝ) ^ (6 + ε) := by
  rcases hmod with ⟨C, hC, hbound⟩
  refine ⟨C, hC, fun W hW ↦ ?_⟩
  have hid : (1728 : ℝ) * (W.Δ : ℝ) = (W.c₄ : ℝ) ^ 3 - (W.c₆ : ℝ) ^ 2 := by
    exact_mod_cast (by
      simp only [WeierstrassCurve.Δ, WeierstrassCurve.c₄, WeierstrassCurve.c₆,
        WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      ring : (1728 : ℤ) * W.Δ = W.c₄ ^ 3 - W.c₆ ^ 2)
  have habs : ∀ z : ℤ, (z.natAbs : ℝ) = |(z : ℝ)| := fun z ↦ by
    rw [show (z.natAbs : ℝ) = ((|z| : ℤ) : ℝ) from Nat.cast_natAbs z, Int.cast_abs]
  have habs_Δ : (W.Δ.natAbs : ℝ) = |(W.Δ : ℝ)| := habs W.Δ
  have habs_c4 : (W.c₄.natAbs : ℝ) = |(W.c₄ : ℝ)| := habs W.c₄
  have habs_c6 : (W.c₆.natAbs : ℝ) = |(W.c₆ : ℝ)| := habs W.c₆
  set M := max ((W.c₄.natAbs : ℝ) ^ 3) ((W.c₆.natAbs : ℝ) ^ 2)
  have hc4_le : |(W.c₄ : ℝ)| ^ 3 ≤ M := by rw [← habs_c4]; exact le_max_left _ _
  have hc6_le : |(W.c₆ : ℝ)| ^ 2 ≤ M := by rw [← habs_c6]; exact le_max_right _ _
  have h1728 : 1728 * |(W.Δ : ℝ)| ≤ 2 * M := by
    calc 1728 * |(W.Δ : ℝ)|
        = |(1728 : ℝ) * (W.Δ : ℝ)| := by rw [abs_mul]; norm_num
      _ = |(W.c₄ : ℝ) ^ 3 - (W.c₆ : ℝ) ^ 2| := by rw [hid]
      _ ≤ |(W.c₄ : ℝ) ^ 3| + |(W.c₆ : ℝ) ^ 2| := abs_sub _ _
      _ = |(W.c₄ : ℝ)| ^ 3 + |(W.c₆ : ℝ)| ^ 2 := by rw [abs_pow, abs_pow]
      _ ≤ 2 * M := by linarith
  have hM := hbound W hW
  linarith [abs_nonneg (W.Δ : ℝ)]

end SzpiroConjecture
