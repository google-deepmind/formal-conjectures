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

public import FormalConjecturesForMathlib.Algebra.CubicDiscriminant
public import FormalConjecturesForMathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import FormalConjecturesForMathlib.Analysis.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Analysis.Polynomial.Order
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

@[expose] public noncomputable section

/-!
# The real period of an elliptic curve as an integral

Let $E$ be an elliptic curve over $\mathbb{R}$ with Weierstrass equation
$y^2 + a_1 xy + a_3 y = x^3 + a_2 x^2 + a_4 x + a_6$ and invariant differential
$\omega = \frac{dx}{2y + a_1 x + a_3}$. Completing the square,
$(2y + a_1 x + a_3)^2 = 4x^3 + b_2 x^2 + 2 b_4 x + b_6 =: F(x)$, the *two-torsion cubic*
`WeierstrassCurve.twoTorsionPolynomial`. The real locus $E(\mathbb{R})$ consists of the point at
infinity and the real points with $F(x) \geq 0$; over $F(x) > 0$ it has the two branches
$2y + a_1 x + a_3 = \pm\sqrt{F(x)}$, on each of which $|\omega| = \frac{dx}{\sqrt{F(x)}}$. Hence
the **real period** of the Birch and Swinnerton-Dyer conjecture is
$$\Omega_E = \int_{E(\mathbb{R})} |\omega| = 2 \int_{\mathbb{R}} \frac{dx}{\sqrt{F(x)}},$$
with the integrand taken to be $0$ where $F \leq 0$.

This file defines
* `WeierstrassCurve.realPeriodIntegrand`, the density $x \mapsto 1 / \sqrt{F(x)}$, with the junk
  value $0$ where $F \leq 0$;
* `WeierstrassCurve.realPeriodIntegral`, the real period $2 \int_{\mathbb{R}} dx / \sqrt{F(x)}$;
* `WeierstrassCurve.e₁`, the largest real root of the two-torsion cubic;
* `WeierstrassCurve.leastRealPeriodIntegral`, the integral $2 \int_{e_1}^\infty dx / \sqrt{F(x)}$
  over the identity component $E(\mathbb{R})^0 = \{x \geq e_1\} \cup \{O\}$, the least positive
  real period of the period lattice;

and proves that for an elliptic curve the integrand is integrable
(`WeierstrassCurve.integrable_realPeriodIntegrand`) and that
$$\Omega_E = c_\infty \cdot 2 \int_{e_1}^\infty \frac{dx}{\sqrt{F(x)}},$$
where $c_\infty$ is $2$ if $\Delta > 0$ (`WeierstrassCurve.realPeriodIntegral_of_pos`) and $1$
if $\Delta < 0$ (`WeierstrassCurve.realPeriodIntegral_of_neg`), so that the real period is
positive (`WeierstrassCurve.realPeriodIntegral_pos`). When $\Delta < 0$ the cubic has the single
real root $e_1$ (`WeierstrassCurve.eq_e₁_of_isRoot_of_neg`) and the integrand vanishes on
$(-\infty, e_1]$. When $\Delta > 0$ it has three real roots
$e_3 < e_2 < e_1$ (`WeierstrassCurve.exists_three_roots_of_pos`) and the bounded component
$\{e_3 \leq x \leq e_2\}$ contributes as much as the identity component, the second equality in
DLMF 23.6.34: translation by the two-torsion point $(e_2, 0)$ maps $E(\mathbb{R})^0$ onto the
bounded component and preserves $\omega$. On $x$-coordinates it is the involution
`WeierstrassCurve.ovalMap`, $x \mapsto e_2 - (e_1 - e_2)(e_2 - e_3) / (x - e_2)$, exchanging
$(e_1, \infty)$ and $(e_3, e_2)$ with $F(\varphi(x)) = \varphi'(x)^2 F(x)$
(`WeierstrassCurve.setIntegral_realPeriodIntegrand_Ioo`).

*Convention.* `WeierstrassCurve.realPeriodIntegral` is $\int_{E(\mathbb{R})} |\omega|$, the
LMFDB convention, which absorbs the real Tamagawa number $c_\infty$, the number of connected
components of $E(\mathbb{R})$. A Birch and Swinnerton-Dyer statement using it must therefore take
the Tamagawa product over the *finite* places only. The other convention pairs
`WeierstrassCurve.leastRealPeriodIntegral` with a product over *all* places. The two give the same
number, but mixing them miscounts by a factor of $2$ when $\Delta > 0$.

*References:*
- [LMFDB](https://beta.lmfdb.org/knowledge/show/ec.period), knowls `ec.period`,
  `ec.q.real_period` and `ec.q.period_lattice`
- [DLMF](https://dlmf.nist.gov/23.6.iv), §23.5 and §23.6(iv), equations 23.6.34 and 23.6.36
- [Cre1997] John E. Cremona. Algorithms for Modular Elliptic Curves, 2nd edition, Section 3.7,
    https://johncremona.github.io/book/fulltext/index.html
- [Sil2009] Joseph H. Silverman. The Arithmetic of Elliptic Curves, 2nd edition, Chapter VI,
    https://link.springer.com/book/10.1007/978-0-387-09494-6
- [Sil1994] Joseph H. Silverman. Advanced Topics in the Arithmetic of Elliptic Curves,
    Chapter V §2, https://link.springer.com/book/10.1007/978-1-4612-0851-8
-/

open Filter MeasureTheory Polynomial Set

namespace WeierstrassCurve

variable (W : WeierstrassCurve ℝ)

/- ## The largest real root -/

/-- The largest real root $e_1$ of the two-torsion cubic $4x^3 + b_2 x^2 + 2 b_4 x + b_6$. A real
cubic has a real root, so this is a root, and the greatest one. If the discriminant is positive all
three roots $e_1 > e_2 > e_3$ are real; if it is negative, $e_1$ is the only real root. -/
def e₁ : ℝ := sSup {x : ℝ | W.twoTorsionPolynomial.toPoly.IsRoot x}

lemma finite_setOf_isRoot_twoTorsionPolynomial :
    {x : ℝ | W.twoTorsionPolynomial.toPoly.IsRoot x}.Finite :=
  finite_setOfPred_isRoot W.toPoly_twoTorsionPolynomial_ne_zero

lemma isRoot_e₁ : W.twoTorsionPolynomial.toPoly.IsRoot W.e₁ :=
  Set.Nonempty.csSup_mem
    (exists_isRoot_of_odd_natDegree (by rw [W.natDegree_toPoly_twoTorsionPolynomial]; decide))
    W.finite_setOf_isRoot_twoTorsionPolynomial

lemma le_e₁_of_isRoot {x : ℝ} (hx : W.twoTorsionPolynomial.toPoly.IsRoot x) : x ≤ W.e₁ :=
  le_csSup W.finite_setOf_isRoot_twoTorsionPolynomial.bddAbove hx

/-- A root with no root to its right is $e_1$. -/
lemma e₁_eq_of_isRoot {e : ℝ} (he : W.twoTorsionPolynomial.toPoly.IsRoot e)
    (h : ∀ x, e < x → ¬ W.twoTorsionPolynomial.toPoly.IsRoot x) : W.e₁ = e :=
  le_antisymm (not_lt.mp fun hlt ↦ h _ hlt W.isRoot_e₁) (W.le_e₁_of_isRoot he)

/-- The two-torsion cubic is positive to the right of $e_1$. -/
lemma eval_toPoly_twoTorsionPolynomial_pos {x : ℝ} (hx : W.e₁ < x) :
    0 < W.twoTorsionPolynomial.toPoly.eval x :=
  zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg
    (fun r hr ↦ (W.le_e₁_of_isRoot hr).trans_lt hx)
    (by rw [W.leadingCoeff_toPoly_twoTorsionPolynomial]; norm_num)

/-- The two-torsion cubic is nonpositive to the left of all of its roots: it has odd degree and
positive leading coefficient. -/
lemma eval_toPoly_twoTorsionPolynomial_nonpos {x : ℝ}
    (hx : ∀ r, W.twoTorsionPolynomial.toPoly.IsRoot r → x ≤ r) :
    W.twoTorsionPolynomial.toPoly.eval x ≤ 0 := by
  have h := zero_le_negOnePow_mul_eval_of_le_roots_of_leadingCoeff_nonneg hx
    (by rw [W.leadingCoeff_toPoly_twoTorsionPolynomial]; norm_num)
  rw [W.natDegree_toPoly_twoTorsionPolynomial] at h
  norm_num at h
  linarith

/-- For an elliptic curve $e_1$ is a simple root of the two-torsion cubic, whose discriminant is
$16 \Delta \neq 0$. -/
lemma rootMultiplicity_e₁ [W.IsElliptic] :
    rootMultiplicity W.e₁ W.twoTorsionPolynomial.toPoly = 1 :=
  le_antisymm
    (Cubic.rootMultiplicity_le_one_of_discr_ne_zero four_ne_zero
      (W.twoTorsionPolynomial_discr_ne_zero_of_isElliptic (isUnit_iff_ne_zero.mpr two_ne_zero)) _)
    ((rootMultiplicity_pos W.toPoly_twoTorsionPolynomial_ne_zero).mpr W.isRoot_e₁)

/-- The two-torsion cubic of an elliptic curve factors as $(x - e_1) Q(x)$ with $Q$ positive on
$[e_1, \infty)$. -/
lemma exists_toPoly_twoTorsionPolynomial_eq_X_sub_C_mul [W.IsElliptic] : ∃ Q : ℝ[X],
    W.twoTorsionPolynomial.toPoly = (X - C W.e₁) * Q ∧ ∀ x, W.e₁ ≤ x → 0 < Q.eval x := by
  obtain ⟨Q, hQ, hdvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd
    W.twoTorsionPolynomial.toPoly W.toPoly_twoTorsionPolynomial_ne_zero W.e₁
  rw [W.rootMultiplicity_e₁, pow_one] at hQ
  refine ⟨Q, hQ, fun x hx ↦ zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg (fun r hr ↦ ?_) ?_⟩
  · have hrF : W.twoTorsionPolynomial.toPoly.IsRoot r := by
      rw [IsRoot, hQ, eval_mul, hr.eq_zero, mul_zero]
    exact ((W.le_e₁_of_isRoot hrF).lt_of_ne fun h ↦ hdvd (dvd_iff_isRoot.mpr (h ▸ hr))).trans_le hx
  · rw [← leadingCoeff_monic_mul (monic_X_sub_C W.e₁), ← hQ,
      W.leadingCoeff_toPoly_twoTorsionPolynomial]
    norm_num

/-- **When $\Delta < 0$ the two-torsion cubic has $e_1$ as its only real root.** Otherwise it
would have two distinct real roots, hence split over $\mathbb{R}$, forcing its discriminant
$16 \Delta$ to be nonnegative. -/
lemma eq_e₁_of_isRoot_of_neg (h : W.Δ < 0) {x : ℝ}
    (hx : W.twoTorsionPolynomial.toPoly.IsRoot x) : x = W.e₁ := by
  have : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr h.ne⟩
  by_contra hne
  obtain ⟨Q, hQ, -⟩ := W.exists_toPoly_twoTorsionPolynomial_eq_X_sub_C_mul
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    exact W.toPoly_twoTorsionPolynomial_ne_zero (by simp [hQ])
  have hQdeg : Q.natDegree = 2 := by
    have h3 := W.natDegree_toPoly_twoTorsionPolynomial
    rw [hQ, natDegree_mul (X_sub_C_ne_zero W.e₁) hQ0, natDegree_X_sub_C] at h3
    omega
  have hQx : Q.IsRoot x := by
    have hx' := hx
    rw [IsRoot, hQ, eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero] at hx'
    exact hx'.resolve_left (sub_ne_zero.mpr hne)
  obtain ⟨S, hS⟩ := dvd_iff_isRoot.mpr hQx
  have hS0 : S ≠ 0 := by rintro rfl; simp [hS] at hQ0
  have hSdeg : S.natDegree = 1 := by
    rw [hS, natDegree_mul (X_sub_C_ne_zero x) hS0, natDegree_X_sub_C] at hQdeg
    omega
  have hsplits : (W.twoTorsionPolynomial.toPoly.map (RingHom.id ℝ)).Splits := by
    rw [Polynomial.map_id, hQ, hS]
    exact (Splits.X_sub_C _).mul ((Splits.X_sub_C _).mul
      (Splits.of_natDegree_le_one_of_invertible hSdeg.le
        (invertibleOfNonzero (leadingCoeff_ne_zero.mpr hS0))))
  have hd := Cubic.discr_nonneg_of_splits (P := W.twoTorsionPolynomial) four_ne_zero hsplits
  rw [W.twoTorsionPolynomial_discr] at hd
  linarith

/- ## The three real roots when Δ > 0 -/

/-- Dividing the two-torsion cubic by $x - e_1$: the quotient is the quadratic
$4x^2 + (b_2 + 4e_1) x + (2b_4 + b_2 e_1 + 4e_1^2)$. -/
lemma toPoly_twoTorsionPolynomial_eq_X_sub_C_e₁_mul :
    W.twoTorsionPolynomial.toPoly = (X - C W.e₁) *
      (C 4 * X ^ 2 + C (W.b₂ + 4 * W.e₁) * X + C (2 * W.b₄ + W.b₂ * W.e₁ + 4 * W.e₁ ^ 2)) := by
  have h := W.isRoot_e₁
  rw [IsRoot, eval_toPoly_twoTorsionPolynomial] at h
  refine Polynomial.funext fun x ↦ ?_
  simp only [eval_toPoly_twoTorsionPolynomial, eval_mul, eval_sub, eval_add, eval_X, eval_C,
    eval_pow]
  linear_combination h

/-- The discriminant $16 \Delta$ of the two-torsion cubic $(x - e_1) Q(x)$ is $Q(e_1)^2$ times the
discriminant of the quadratic $Q$. -/
lemma sixteen_mul_Δ_eq_sq_mul : 16 * W.Δ =
    (4 * W.e₁ ^ 2 + (W.b₂ + 4 * W.e₁) * W.e₁ + (2 * W.b₄ + W.b₂ * W.e₁ + 4 * W.e₁ ^ 2)) ^ 2 *
      ((W.b₂ + 4 * W.e₁) ^ 2 - 16 * (2 * W.b₄ + W.b₂ * W.e₁ + 4 * W.e₁ ^ 2)) := by
  have h := W.isRoot_e₁
  rw [IsRoot, eval_toPoly_twoTorsionPolynomial] at h
  have hb₆ : W.b₆ = -(4 * W.e₁ ^ 3 + W.b₂ * W.e₁ ^ 2 + 2 * W.b₄ * W.e₁) := by linarith
  rw [← W.twoTorsionPolynomial_discr]
  simp only [twoTorsionPolynomial, Cubic.discr, hb₆]
  ring

/-- **When $\Delta > 0$ the two-torsion cubic has three distinct real roots** $e_3 < e_2 < e_1$:
the quadratic cofactor of $x - e_1$ has positive discriminant, and $e_1$ is not among its roots. -/
lemma exists_three_roots_of_pos (h : 0 < W.Δ) : ∃ e₂ e₃ : ℝ, e₃ < e₂ ∧ e₂ < W.e₁ ∧
    W.twoTorsionPolynomial.toPoly = C 4 * ((X - C W.e₁) * ((X - C e₂) * (X - C e₃))) := by
  have hid := W.sixteen_mul_Δ_eq_sq_mul
  set q₁ := W.b₂ + 4 * W.e₁ with hq₁
  set q₀ := 2 * W.b₄ + W.b₂ * W.e₁ + 4 * W.e₁ ^ 2 with hq₀
  have hdisc : 0 < q₁ ^ 2 - 16 * q₀ := by
    by_contra! hle
    have := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (4 * W.e₁ ^ 2 + q₁ * W.e₁ + q₀)) hle
    linarith
  have hQe : 4 * W.e₁ ^ 2 + q₁ * W.e₁ + q₀ ≠ 0 := by
    intro h0
    rw [h0] at hid
    linarith
  set s := √(q₁ ^ 2 - 16 * q₀) with hs_def
  have hs : s ^ 2 = q₁ ^ 2 - 16 * q₀ := Real.sq_sqrt hdisc.le
  have hspos : 0 < s := Real.sqrt_pos.mpr hdisc
  have hQ : C 4 * X ^ 2 + C q₁ * X + C q₀ =
      C 4 * ((X - C ((-q₁ + s) / 8)) * (X - C ((-q₁ - s) / 8))) := by
    refine Polynomial.funext fun x ↦ ?_
    simp only [eval_mul, eval_sub, eval_add, eval_X, eval_C, eval_pow]
    linear_combination (1 / 16) * hs
  refine ⟨(-q₁ + s) / 8, (-q₁ - s) / 8, by linarith, ?_, ?_⟩
  · have hroot : W.twoTorsionPolynomial.toPoly.IsRoot ((-q₁ + s) / 8) := by
      rw [IsRoot, W.toPoly_twoTorsionPolynomial_eq_X_sub_C_e₁_mul, hQ]
      simp
    refine (W.le_e₁_of_isRoot hroot).lt_of_ne fun heq ↦ hQe ?_
    have := congrArg (eval W.e₁) hQ
    simp only [eval_mul, eval_sub, eval_add, eval_X, eval_C, eval_pow] at this
    rw [this, heq]
    ring
  · rw [W.toPoly_twoTorsionPolynomial_eq_X_sub_C_e₁_mul, hQ]
    ring

variable {e₂ e₃ : ℝ}

lemma eval_toPoly_twoTorsionPolynomial_of_factor
    (hF : W.twoTorsionPolynomial.toPoly = C 4 * ((X - C W.e₁) * ((X - C e₂) * (X - C e₃))))
    (x : ℝ) : W.twoTorsionPolynomial.toPoly.eval x = 4 * (x - W.e₁) * (x - e₂) * (x - e₃) := by
  rw [hF]
  simp only [eval_mul, eval_sub, eval_X, eval_C]
  ring

/- ## The integrand -/

/-- The density $|\omega| / dx = 1 / \sqrt{4x^3 + b_2 x^2 + 2 b_4 x + b_6}$ of the invariant
differential on either branch of the real locus, as a function on $\mathbb{R}$, with the junk value
$0$ where the cubic is not positive. -/
def realPeriodIntegrand (x : ℝ) : ℝ := (√(W.twoTorsionPolynomial.toPoly.eval x))⁻¹

lemma realPeriodIntegrand_nonneg (x : ℝ) : 0 ≤ W.realPeriodIntegrand x :=
  inv_nonneg.mpr (Real.sqrt_nonneg _)

lemma realPeriodIntegrand_pos {x : ℝ} (hx : W.e₁ < x) : 0 < W.realPeriodIntegrand x :=
  inv_pos.mpr (Real.sqrt_pos.mpr (W.eval_toPoly_twoTorsionPolynomial_pos hx))

/-- The integrand takes its junk value $0$ where the two-torsion cubic is not positive: the square
root of a nonpositive number is $0$, and $0^{-1} = 0$. -/
lemma realPeriodIntegrand_eq_zero {x : ℝ} (hx : W.twoTorsionPolynomial.toPoly.eval x ≤ 0) :
    W.realPeriodIntegrand x = 0 := by
  rw [realPeriodIntegrand, Real.sqrt_eq_zero_of_nonpos hx, inv_zero]

/-- When $\Delta < 0$ the integrand vanishes on all of $(-\infty, e_1]$, since $e_1$ is then the
only real root of the two-torsion cubic. -/
lemma realPeriodIntegrand_eq_zero_of_le_e₁ (h : W.Δ < 0) {x : ℝ} (hx : x ≤ W.e₁) :
    W.realPeriodIntegrand x = 0 :=
  W.realPeriodIntegrand_eq_zero <| W.eval_toPoly_twoTorsionPolynomial_nonpos fun _ hr ↦
    W.eq_e₁_of_isRoot_of_neg h hr ▸ hx

/-- When the cubic has the three real roots $e_3 < e_2 < e_1$, the integrand vanishes on
$(-\infty, e_1]$ outside the bounded component $(e_3, e_2)$, where the cubic is nonpositive. -/
lemma realPeriodIntegrand_eq_zero_of_factor (h₃₂ : e₃ < e₂) (h₂₁ : e₂ < W.e₁)
    (hF : W.twoTorsionPolynomial.toPoly = C 4 * ((X - C W.e₁) * ((X - C e₂) * (X - C e₃))))
    {x : ℝ} (hx : x ≤ W.e₁) (hx' : x ∉ Ioo e₃ e₂) : W.realPeriodIntegrand x = 0 := by
  apply W.realPeriodIntegrand_eq_zero
  rw [W.eval_toPoly_twoTorsionPolynomial_of_factor hF]
  rcases not_and_or.mp hx' with h | h <;> rw [not_lt] at h
  · nlinarith [mul_nonneg (mul_nonneg (show 0 ≤ W.e₁ - x by linarith)
      (show 0 ≤ e₂ - x by linarith)) (show 0 ≤ e₃ - x by linarith)]
  · nlinarith [mul_nonneg (mul_nonneg (show 0 ≤ W.e₁ - x by linarith)
      (show 0 ≤ x - e₂ by linarith)) (show 0 ≤ x - e₃ by linarith)]

lemma measurable_realPeriodIntegrand : Measurable W.realPeriodIntegrand :=
  (Real.continuous_sqrt.comp W.twoTorsionPolynomial.toPoly.continuous).measurable.inv

/- ## Integrability on the identity component -/

/-- Eventually $x^3 \leq 4x^3 + b_2 x^2 + 2 b_4 x + b_6$. -/
lemma eventually_pow_three_le_eval_toPoly_twoTorsionPolynomial :
    ∀ᶠ x in atTop, x ^ 3 ≤ W.twoTorsionPolynomial.toPoly.eval x := by
  have h := W.twoTorsionPolynomial.toPoly.isEquivalent_atTop_lead.isLittleO.def
    (by norm_num : (0 : ℝ) < 1 / 2)
  simp only [W.natDegree_toPoly_twoTorsionPolynomial,
    W.leadingCoeff_toPoly_twoTorsionPolynomial, Pi.sub_apply, Real.norm_eq_abs] at h
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * x ^ 3)] at hx
  linarith [(abs_le.mp hx).1, pow_nonneg hx0 3]

/-- Integrability at infinity: the integrand is integrable on $(c, \infty)$ as soon as
$x^3 \leq F(x)$ holds there. -/
lemma integrableOn_realPeriodIntegrand_Ioi {c : ℝ} (hc : 0 < c)
    (h : ∀ x, c ≤ x → x ^ 3 ≤ W.twoTorsionPolynomial.toPoly.eval x) :
    IntegrableOn W.realPeriodIntegrand (Ioi c) := by
  refine (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 / 2 : ℝ) < -1) hc).mono'
    W.measurable_realPeriodIntegrand.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : (0 : ℝ) < x := hc.trans hx
  rw [Real.norm_eq_abs, abs_of_nonneg (W.realPeriodIntegrand_nonneg x),
    show x ^ (-3 / 2 : ℝ) = (√(x ^ 3))⁻¹ by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast x 3, ← Real.rpow_mul hx0.le,
        ← Real.rpow_neg hx0.le]
      norm_num]
  exact inv_anti₀ (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_le_sqrt (h x hx.le))

/-- Integrability at the simple root $e_1$: there $F(x) = (x - e_1) Q(x)$ with $Q$ positive, so the
integrand is $(x - e_1)^{-1/2}$ times a continuous function. -/
lemma integrableOn_realPeriodIntegrand_Ioc [W.IsElliptic] {c : ℝ} (hc : W.e₁ ≤ c) :
    IntegrableOn W.realPeriodIntegrand (Ioc W.e₁ c) := by
  obtain ⟨Q, hQ, hQpos⟩ := W.exists_toPoly_twoTorsionPolynomial_eq_X_sub_C_mul
  have hr : IntegrableOn (fun x : ℝ ↦ (x - W.e₁) ^ (-(1 / 2) : ℝ)) (Icc W.e₁ c) := by
    refine (intervalIntegrable_iff_integrableOn_Icc_of_le hc).mp ?_
    simpa only [zero_add, sub_add_cancel] using
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := c - W.e₁)
        (by norm_num : (-1 : ℝ) < -(1 / 2))).comp_sub_right W.e₁
  have hg : ContinuousOn (fun x : ℝ ↦ (√(Q.eval x))⁻¹) (Icc W.e₁ c) :=
    (Real.continuous_sqrt.comp Q.continuous).continuousOn.inv₀ fun x hx ↦
      (Real.sqrt_pos.mpr (hQpos x hx.1)).ne'
  refine ((hr.mul_continuousOn hg isCompact_Icc).mono_set Ioc_subset_Icc_self).congr_fun
    (fun x hx ↦ ?_) measurableSet_Ioc
  have hx1 : (0 : ℝ) ≤ x - W.e₁ := sub_nonneg.mpr hx.1.le
  change (x - W.e₁) ^ (-(1 / 2) : ℝ) * (√(Q.eval x))⁻¹ = _
  rw [realPeriodIntegrand, hQ, eval_mul, eval_sub, eval_X, eval_C, Real.sqrt_mul hx1, mul_inv,
    Real.rpow_neg hx1, ← Real.sqrt_eq_rpow]

/-- The integrand is integrable on $(e_1, \infty)$. -/
lemma integrableOn_realPeriodIntegrand [W.IsElliptic] :
    IntegrableOn W.realPeriodIntegrand (Ioi W.e₁) := by
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp W.eventually_pow_three_le_eval_toPoly_twoTorsionPolynomial
  have hec : W.e₁ ≤ max R₀ (max W.e₁ 1) := le_max_of_le_right (le_max_left _ _)
  rw [← Ioc_union_Ioi_eq_Ioi hec]
  exact (W.integrableOn_realPeriodIntegrand_Ioc hec).union
    (W.integrableOn_realPeriodIntegrand_Ioi
      (zero_lt_one.trans_le (le_max_of_le_right (le_max_right _ _)))
      fun x hx ↦ hR₀ x ((le_max_left _ _).trans hx))

/- ## Translation by a two-torsion point -/

/-- The $x$-coordinate of translation by the two-torsion point $(e_2, 0)$, for a cubic with real
roots $e_3 < e_2 < e_1$: the involution $x \mapsto e_2 - (e_1 - e_2)(e_2 - e_3) / (x - e_2)$,
which exchanges the identity component $(e_1, \infty)$ and the bounded component $(e_3, e_2)$. -/
def ovalMap (e₁ e₂ e₃ x : ℝ) : ℝ := e₂ - (e₁ - e₂) * (e₂ - e₃) / (x - e₂)

section ovalMap

variable {e₁ : ℝ}

lemma hasDerivAt_ovalMap {x : ℝ} (hx : x ≠ e₂) :
    HasDerivAt (ovalMap e₁ e₂ e₃) ((e₁ - e₂) * (e₂ - e₃) / (x - e₂) ^ 2) x := by
  have h := ((((hasDerivAt_id' x).sub_const e₂).inv (sub_ne_zero.mpr hx)).const_mul
    ((e₁ - e₂) * (e₂ - e₃))).const_sub e₂
  refine (h.congr_deriv (by ring)).congr_of_eventuallyEq (Eventually.of_forall fun y ↦ ?_)
  simp [ovalMap, div_eq_mul_inv]

lemma ovalMap_ovalMap (hk : (e₁ - e₂) * (e₂ - e₃) ≠ 0) (x : ℝ) :
    ovalMap e₁ e₂ e₃ (ovalMap e₁ e₂ e₃ x) = x := by
  rw [ovalMap, ovalMap, sub_sub_cancel_left, div_neg, div_div_eq_mul_div,
    mul_div_cancel_left₀ _ hk]
  ring

lemma ovalMap_mem_Ioo (h₃₂ : e₃ < e₂) (h₂₁ : e₂ < e₁) {x : ℝ} (hx : e₁ < x) :
    ovalMap e₁ e₂ e₃ x ∈ Ioo e₃ e₂ := by
  have hu : 0 < x - e₂ := by linarith
  have hk : 0 < (e₁ - e₂) * (e₂ - e₃) := mul_pos (by linarith) (by linarith)
  have h1 : (e₁ - e₂) * (e₂ - e₃) / (x - e₂) < e₂ - e₃ := by
    rw [div_lt_iff₀ hu]
    nlinarith [mul_lt_mul_of_pos_left (show e₁ - e₂ < x - e₂ by linarith)
      (show 0 < e₂ - e₃ by linarith)]
  have h2 := div_pos hk hu
  constructor <;> (rw [ovalMap]; linarith)

lemma lt_ovalMap (h₂₁ : e₂ < e₁) {y : ℝ} (hy : y ∈ Ioo e₃ e₂) : e₁ < ovalMap e₁ e₂ e₃ y := by
  have hu : 0 < e₂ - y := by linarith [hy.2]
  have h1 : e₁ - e₂ < (e₁ - e₂) * (e₂ - e₃) / (e₂ - y) := by
    rw [lt_div_iff₀ hu]
    nlinarith [mul_lt_mul_of_pos_left (show e₂ - y < e₂ - e₃ by linarith [hy.1])
      (show 0 < e₁ - e₂ by linarith)]
  have hneg : y - e₂ = -(e₂ - y) := by ring
  rw [ovalMap, hneg, div_neg]
  linarith

lemma image_ovalMap_Ioi (h₃₂ : e₃ < e₂) (h₂₁ : e₂ < e₁) :
    ovalMap e₁ e₂ e₃ '' Ioi e₁ = Ioo e₃ e₂ := by
  have hk : (e₁ - e₂) * (e₂ - e₃) ≠ 0 := (mul_pos (by linarith) (by linarith)).ne'
  refine subset_antisymm ?_ fun y hy ↦
    ⟨ovalMap e₁ e₂ e₃ y, lt_ovalMap h₂₁ hy, ovalMap_ovalMap hk y⟩
  rintro _ ⟨x, hx, rfl⟩
  exact ovalMap_mem_Ioo h₃₂ h₂₁ hx

lemma injOn_ovalMap (h₃₂ : e₃ < e₂) (h₂₁ : e₂ < e₁) : InjOn (ovalMap e₁ e₂ e₃) (Ioi e₁) := by
  have hk : (e₁ - e₂) * (e₂ - e₃) ≠ 0 := (mul_pos (by linarith) (by linarith)).ne'
  intro x _ y _ hxy
  rw [← ovalMap_ovalMap hk x, hxy, ovalMap_ovalMap hk y]

/-- Translation by a two-torsion point preserves the invariant differential: with
$\varphi = $ `ovalMap`, $F(\varphi(x)) = \varphi'(x)^2 F(x)$, so
$|\varphi'(x)| / \sqrt{F(\varphi(x))} = 1 / \sqrt{F(x)}$. -/
lemma abs_mul_inv_sqrt_ovalMap (h₃₂ : e₃ < e₂) (h₂₁ : e₂ < e₁) {x : ℝ} (hx : e₁ < x) :
    |(e₁ - e₂) * (e₂ - e₃) / (x - e₂) ^ 2| *
      (√(4 * (ovalMap e₁ e₂ e₃ x - e₁) * (ovalMap e₁ e₂ e₃ x - e₂) *
        (ovalMap e₁ e₂ e₃ x - e₃)))⁻¹ =
      (√(4 * (x - e₁) * (x - e₂) * (x - e₃)))⁻¹ := by
  have hu : x - e₂ ≠ 0 := sub_ne_zero.mpr (h₂₁.trans hx).ne'
  have hk : 0 < (e₁ - e₂) * (e₂ - e₃) := mul_pos (by linarith) (by linarith)
  set c := (e₁ - e₂) * (e₂ - e₃) / (x - e₂) ^ 2 with hc
  have hcpos : 0 < c := div_pos hk (by positivity)
  have key : 4 * (ovalMap e₁ e₂ e₃ x - e₁) * (ovalMap e₁ e₂ e₃ x - e₂) *
      (ovalMap e₁ e₂ e₃ x - e₃) = c ^ 2 * (4 * (x - e₁) * (x - e₂) * (x - e₃)) := by
    simp only [ovalMap, hc]
    field_simp
    ring
  rw [key, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hcpos.le, abs_of_pos hcpos, mul_inv,
    ← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul]

end ovalMap

/- ## The bounded component -/

/-- **The bounded component contributes as much as the identity component** (the second equality
in DLMF 23.6.34): the substitution $x = \varphi(t)$, $t \in (e_1, \infty)$, in
$\int_{e_3}^{e_2} dx / \sqrt{F(x)}$. -/
lemma setIntegral_realPeriodIntegrand_Ioo (h₃₂ : e₃ < e₂) (h₂₁ : e₂ < W.e₁)
    (hF : W.twoTorsionPolynomial.toPoly = C 4 * ((X - C W.e₁) * ((X - C e₂) * (X - C e₃)))) :
    ∫ x in Ioo e₃ e₂, W.realPeriodIntegrand x = ∫ x in Ioi W.e₁, W.realPeriodIntegrand x := by
  rw [← image_ovalMap_Ioi h₃₂ h₂₁, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun x hx ↦ (hasDerivAt_ovalMap (h₂₁.trans hx).ne').hasDerivWithinAt) (injOn_ovalMap h₃₂ h₂₁)]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
  simp only [smul_eq_mul, realPeriodIntegrand, W.eval_toPoly_twoTorsionPolynomial_of_factor hF]
  exact abs_mul_inv_sqrt_ovalMap h₃₂ h₂₁ hx

lemma integrableOn_realPeriodIntegrand_Ioo [W.IsElliptic] (h₃₂ : e₃ < e₂) (h₂₁ : e₂ < W.e₁)
    (hF : W.twoTorsionPolynomial.toPoly = C 4 * ((X - C W.e₁) * ((X - C e₂) * (X - C e₃)))) :
    IntegrableOn W.realPeriodIntegrand (Ioo e₃ e₂) := by
  rw [← image_ovalMap_Ioi h₃₂ h₂₁, integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi (fun x hx ↦ (hasDerivAt_ovalMap (h₂₁.trans hx).ne').hasDerivWithinAt)
    (injOn_ovalMap h₃₂ h₂₁)]
  refine W.integrableOn_realPeriodIntegrand.congr_fun (fun x hx ↦ ?_) measurableSet_Ioi
  simp only [smul_eq_mul, realPeriodIntegrand, W.eval_toPoly_twoTorsionPolynomial_of_factor hF]
  exact (abs_mul_inv_sqrt_ovalMap h₃₂ h₂₁ hx).symm

/- ## Integrability on the whole line -/

/-- When $\Delta < 0$ the integrand is integrable on $(-\infty, e_1]$, where it vanishes. -/
lemma integrableOn_realPeriodIntegrand_Iic_of_neg (h : W.Δ < 0) :
    IntegrableOn W.realPeriodIntegrand (Iic W.e₁) :=
  integrableOn_zero.congr_fun (fun _ hx ↦ (W.realPeriodIntegrand_eq_zero_of_le_e₁ h hx).symm)
    measurableSet_Iic

lemma setIntegral_realPeriodIntegrand_Iic_of_neg (h : W.Δ < 0) :
    ∫ x in Iic W.e₁, W.realPeriodIntegrand x = 0 :=
  setIntegral_eq_zero_of_forall_eq_zero fun _ hx ↦ W.realPeriodIntegrand_eq_zero_of_le_e₁ h hx

/-- When $\Delta > 0$ the integrand is integrable on $(-\infty, e_1]$: it vanishes there outside
the bounded component $(e_3, e_2)$, on which it is integrable. -/
lemma integrableOn_realPeriodIntegrand_Iic_of_pos (h : 0 < W.Δ) :
    IntegrableOn W.realPeriodIntegrand (Iic W.e₁) := by
  have : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr h.ne'⟩
  obtain ⟨e₂, e₃, h₃₂, h₂₁, hF⟩ := W.exists_three_roots_of_pos h
  exact (W.integrableOn_realPeriodIntegrand_Ioo h₃₂ h₂₁ hF).of_forall_sdiff_eq_zero
    measurableSet_Iic fun x hx ↦ W.realPeriodIntegrand_eq_zero_of_factor h₃₂ h₂₁ hF hx.1 hx.2

/-- When $\Delta > 0$ the integral over $(-\infty, e_1]$ is the integral over the bounded
component, which is the integral over the identity component. -/
lemma setIntegral_realPeriodIntegrand_Iic_of_pos (h : 0 < W.Δ) :
    ∫ x in Iic W.e₁, W.realPeriodIntegrand x = ∫ x in Ioi W.e₁, W.realPeriodIntegrand x := by
  obtain ⟨e₂, e₃, h₃₂, h₂₁, hF⟩ := W.exists_three_roots_of_pos h
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Iic
    (fun x hx ↦ (hx.2.trans h₂₁).le)
    (fun x hx ↦ W.realPeriodIntegrand_eq_zero_of_factor h₃₂ h₂₁ hF hx.1 hx.2),
    W.setIntegral_realPeriodIntegrand_Ioo h₃₂ h₂₁ hF]

lemma integrableOn_realPeriodIntegrand_Iic [W.IsElliptic] :
    IntegrableOn W.realPeriodIntegrand (Iic W.e₁) := by
  rcases lt_or_gt_of_ne (isUnit_iff_ne_zero.mp W.isUnit_Δ) with h | h
  · exact W.integrableOn_realPeriodIntegrand_Iic_of_neg h
  · exact W.integrableOn_realPeriodIntegrand_Iic_of_pos h

/-- The integrand is integrable on $\mathbb{R}$. -/
theorem integrable_realPeriodIntegrand [W.IsElliptic] : Integrable W.realPeriodIntegrand := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := W.e₁)]
  exact W.integrableOn_realPeriodIntegrand_Iic.union W.integrableOn_realPeriodIntegrand

lemma integral_realPeriodIntegrand_eq_add [W.IsElliptic] : ∫ x, W.realPeriodIntegrand x =
    (∫ x in Iic W.e₁, W.realPeriodIntegrand x) + ∫ x in Ioi W.e₁, W.realPeriodIntegrand x := by
  rw [← setIntegral_univ, ← Iic_union_Ioi (a := W.e₁),
    setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
      W.integrableOn_realPeriodIntegrand_Iic W.integrableOn_realPeriodIntegrand]

/-- When $\Delta < 0$ the integral over $\mathbb{R}$ is the integral over the identity
component $(e_1, \infty)$: $E(\mathbb{R})$ is connected. -/
theorem integral_realPeriodIntegrand_of_neg (h : W.Δ < 0) :
    ∫ x, W.realPeriodIntegrand x = ∫ x in Ioi W.e₁, W.realPeriodIntegrand x := by
  have : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr h.ne⟩
  rw [W.integral_realPeriodIntegrand_eq_add, W.setIntegral_realPeriodIntegrand_Iic_of_neg h,
    zero_add]

/-- When $\Delta > 0$ the integral over $\mathbb{R}$ is twice the integral over the identity
component $(e_1, \infty)$: $E(\mathbb{R})$ has two connected components, each contributing
equally. -/
theorem integral_realPeriodIntegrand_of_pos (h : 0 < W.Δ) :
    ∫ x, W.realPeriodIntegrand x = 2 * ∫ x in Ioi W.e₁, W.realPeriodIntegrand x := by
  have : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr h.ne'⟩
  rw [W.integral_realPeriodIntegrand_eq_add, W.setIntegral_realPeriodIntegrand_Iic_of_pos h,
    two_mul]

/- ## The least positive real period as an integral -/

/-- The least positive real period as an integral,
$2 \int_{e_1}^\infty \frac{dx}{\sqrt{4x^3 + b_2 x^2 + 2 b_4 x + b_6}}$: the integral of $|\omega|$
over the identity component of $E(\mathbb{R})$. -/
def leastRealPeriodIntegral : ℝ := 2 * ∫ x in Ioi W.e₁, W.realPeriodIntegrand x

/-- The least positive real period of an elliptic curve over $\mathbb{R}$ is positive. -/
lemma leastRealPeriodIntegral_pos [W.IsElliptic] : 0 < W.leastRealPeriodIntegral := by
  refine mul_pos two_pos ?_
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall W.realPeriodIntegrand_nonneg) W.integrableOn_realPeriodIntegrand,
    show Function.support W.realPeriodIntegrand ∩ Ioi W.e₁ = Ioi W.e₁ from
      inter_eq_right.mpr fun x hx ↦ (W.realPeriodIntegrand_pos hx).ne', Real.volume_Ioi]
  exact ENNReal.zero_lt_top

/- ## The real period as an integral -/

/-- **The real period as an integral**: the integral of $|\omega|$ over the real locus
$E(\mathbb{R})$, that is $2 \int_{\mathbb{R}} dx / \sqrt{F(x)}$ with the integrand taken to be
$0$ where $F \leq 0$. This is the real period of the Birch and Swinnerton-Dyer conjecture, in the
convention that absorbs the real Tamagawa number. -/
def realPeriodIntegral : ℝ := 2 * ∫ x, W.realPeriodIntegrand x

/-- **When $\Delta > 0$ the real period is twice the least positive real period**:
$E(\mathbb{R})$ has two connected components. -/
theorem realPeriodIntegral_of_pos (h : 0 < W.Δ) :
    W.realPeriodIntegral = 2 * W.leastRealPeriodIntegral := by
  rw [realPeriodIntegral, W.integral_realPeriodIntegrand_of_pos h, leastRealPeriodIntegral]

/-- **When $\Delta < 0$ the real period is the least positive real period**: $E(\mathbb{R})$ is
connected. -/
theorem realPeriodIntegral_of_neg (h : W.Δ < 0) :
    W.realPeriodIntegral = W.leastRealPeriodIntegral := by
  rw [realPeriodIntegral, W.integral_realPeriodIntegrand_of_neg h, leastRealPeriodIntegral]

/-- The real period of an elliptic curve over $\mathbb{R}$ is positive. -/
lemma realPeriodIntegral_pos [W.IsElliptic] : 0 < W.realPeriodIntegral := by
  rcases lt_or_gt_of_ne (isUnit_iff_ne_zero.mp W.isUnit_Δ) with h | h
  · rw [W.realPeriodIntegral_of_neg h]
    exact W.leastRealPeriodIntegral_pos
  · rw [W.realPeriodIntegral_of_pos h]
    exact mul_pos two_pos W.leastRealPeriodIntegral_pos

end WeierstrassCurve
