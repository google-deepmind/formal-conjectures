/-
Copyright 2025 The Formal Conjectures Authors.

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
# Complex uniformisation and the real period of an elliptic curve

A lattice $\Lambda \subseteq \mathbb{C}$ is the period lattice of the elliptic curve
$E_\Lambda : y^2 = x^3 - \frac{g_2}{4} x - \frac{g_3}{4}$, and
$z \mapsto (\wp(z), \frac{1}{2} \wp'(z))$ is an isomorphism
$\mathbb{C} / \Lambda \simeq E_\Lambda(\mathbb{C})$. Conversely every elliptic curve over
$\mathbb{C}$ arises this way, from a lattice determined by $g_2$ and $g_3$. The *real period* of
an elliptic curve over $\mathbb{R}$ is the least positive real element of its period lattice.

Under the uniformisation the invariant differential $\frac{dx}{2y + a_1 x + a_3}$ pulls back to
$dz$, so the elements of $\Lambda$ are the periods of that differential, and the real period is
the length of the identity component of $E(\mathbb{R})$. The period in the Birch and
Swinnerton-Dyer conjecture is $\Omega$ or $2\Omega$, according as the discriminant is negative or
positive. That factor is not treated here.

This file is a skeleton. Every definition is complete, and every lemma a definition depends on is
stated, with the short proofs given and the rest left as `sorry`. Lemmas that no definition needs
are omitted, so the modular forms input to `PeriodPair.weierstrassDiscriminant_ne_zero`, the
addition theorem for $\wp$ behind `PeriodPair.toPoint_add`, and surjectivity of the modular
$j$-function behind `PeriodPair.exists_g₂_g₃` each appear only as the statement that names them.

Nothing here is open mathematics. Every remaining `sorry` is a classical theorem, and all but
`PeriodPair.toPoint_surjective` and `PeriodPair.exists_isLeast_pos_real` are already formalised
in the LeanBridge development, from which this skeleton is drawn.

*References:*
- [Wikipedia (Weierstrass elliptic function)](https://en.wikipedia.org/wiki/Weierstrass_elliptic_function)
- [Wikipedia (Birch and Swinnerton-Dyer conjecture)](https://en.wikipedia.org/wiki/Birch_and_Swinnerton-Dyer_conjecture)
- [Sil2009] Joseph H. Silverman. The Arithmetic of Elliptic Curves, 2nd edition, Chapter VI,
    https://link.springer.com/book/10.1007/978-0-387-09494-6
- [Cre1997] John E. Cremona. Algorithms for Modular Elliptic Curves, 2nd edition, Section 3.7,
    https://johncremona.github.io/book/fulltext/index.html
-/

open scoped ComplexConjugate

noncomputable section

namespace PeriodPair

/- ## The elliptic curve attached to a lattice -/

/-- The discriminant $g_2^3 - 27 g_3^2$ of the Weierstrass equation of a period lattice. The
discriminant of the cubic $4 x^3 - g_2 x - g_3$ is $16$ times this. -/
abbrev weierstrassDiscriminant (L : PeriodPair) : ℂ := L.g₂ ^ 3 - 27 * L.g₃ ^ 2

/-- The discriminant of a period lattice never vanishes. Every lattice is a homothety of
$\mathbb{Z} + \mathbb{Z}\tau$ for some $\tau$ in the upper half plane, where the discriminant is
a nonzero multiple of $E_4^3 - E_6^2$. -/
theorem weierstrassDiscriminant_ne_zero (L : PeriodPair) : L.weierstrassDiscriminant ≠ 0 := by
  sorry

/-- The Weierstrass curve $y^2 = x^3 - \frac{g_2}{4} x - \frac{g_3}{4}$ attached to a period
lattice. It is the image of $\wp'^2 = 4 \wp^3 - g_2 \wp - g_3$ under
$(x, y) = (\wp, \frac{1}{2} \wp')$. -/
def weierstrassCurve (L : PeriodPair) : WeierstrassCurve ℂ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -L.g₂ / 4
  a₆ := -L.g₃ / 4

/-- The discriminant of `PeriodPair.weierstrassCurve` is $g_2^3 - 27 g_3^2$. -/
theorem weierstrassCurve_Δ (L : PeriodPair) :
    L.weierstrassCurve.Δ = L.weierstrassDiscriminant := by
  grind [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, weierstrassCurve]

instance (L : PeriodPair) : L.weierstrassCurve.IsElliptic where
  isUnit := by
    simpa [weierstrassCurve_Δ] using isUnit_iff_ne_zero.mpr (weierstrassDiscriminant_ne_zero L)

/- ## The map from the complex numbers to the curve -/

/-- The point $(\wp(z), \frac{1}{2} \wp'(z))$ lies on the curve of $\Lambda$. This is the
differential equation $\wp'^2 = 4 \wp^3 - g_2 \wp - g_3$, divided by $4$. -/
theorem weierstrassCurve_equation (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    L.weierstrassCurve.toAffine.Equation (℘[L] z) (℘'[L] z / 2) := by
  rw [WeierstrassCurve.Affine.equation_iff, weierstrassCurve]
  linear_combination (L.derivWeierstrassP_sq z hz) / 4

open scoped Classical in
/-- The map $\mathbb{C} \to E_\Lambda(\mathbb{C})$ sending $z$ to
$(\wp(z), \frac{1}{2} \wp'(z))$, and every point of $\Lambda$ to the point at infinity. -/
def toPoint (L : PeriodPair) (z : ℂ) : L.weierstrassCurve.toAffine.Point :=
  if hz : z ∈ L.lattice then 0
  else .some (℘[L] z) (℘'[L] z / 2)
    (WeierstrassCurve.Affine.equation_iff_nonsingular.mp (L.weierstrassCurve_equation hz))

/-- `PeriodPair.toPoint` is $\Lambda$-periodic, so it descends to $\mathbb{C} / \Lambda$. -/
theorem toPoint_add_mem (L : PeriodPair) (z : ℂ) (l : L.lattice) :
    L.toPoint (z + l) = L.toPoint z := by
  by_cases hz : z ∈ L.lattice
  · simp only [toPoint, dif_pos (add_mem hz l.2), dif_pos hz]
  · have hzl : z + (l : ℂ) ∉ L.lattice := fun h ↦ hz (by simpa using sub_mem h l.2)
    simp only [toPoint, dif_neg hzl, dif_neg hz]
    congr 1
    · exact L.weierstrassP_add_coe z l
    · rw [L.derivWeierstrassP_add_coe z l]

/-- **The addition theorem**, in the form the group law needs. The case $\wp(z) \neq \wp(w)$
matches the chord formula `WeierstrassCurve.Affine.Point.add_of_X_ne`, and the case $z = w$
matches the tangent formula `add_of_Y_ne`. Both rest on the addition formulas for $\wp$ and
$\wp'$, which follow from Euler's differential-equation argument. -/
theorem toPoint_add (L : PeriodPair) (z w : ℂ) :
    L.toPoint (z + w) = L.toPoint z + L.toPoint w := by sorry

/-- `PeriodPair.toPoint` is surjective. The content is that $\wp$ attains every complex value:
if $\wp - c$ had no zero then $\frac{1}{\wp - c}$ would be entire and doubly periodic, hence
constant by Liouville. The sign of $\frac{1}{2} \wp'(z)$ is then fixed by replacing $z$ by $-z$.

In the LeanBridge development this is reduced to the statement that $\wp$ is surjective, which is
the one statement there still to be proved. -/
theorem toPoint_surjective (L : PeriodPair) : Function.Surjective L.toPoint := by sorry

/- ## Descent to the quotient, and the isomorphism -/

/-- The uniformisation map $\varphi : \mathbb{C} / \Lambda \to E_\Lambda(\mathbb{C})$. -/
def uniformization (L : PeriodPair) :
    (ℂ ⧸ L.lattice.toAddSubgroup) → L.weierstrassCurve.toAffine.Point := by
  refine fun q ↦ Quotient.liftOn' q L.toPoint ?_
  intro a b hab
  rw [QuotientAddGroup.leftRel_apply, Submodule.mem_toAddSubgroup] at hab
  have h := L.toPoint_add_mem a ⟨b - a, by simpa [sub_eq_neg_add] using hab⟩
  simpa [add_sub_cancel] using h.symm

/-- $\varphi(0)$ is the point at infinity. -/
theorem uniformization_zero (L : PeriodPair) : L.uniformization 0 = 0 := by
  show L.toPoint 0 = _
  simp only [toPoint, dif_pos (zero_mem _)]

/-- $\varphi$ is additive, by descent from `PeriodPair.toPoint_add`. -/
theorem uniformization_add (L : PeriodPair) (q p : ℂ ⧸ L.lattice.toAddSubgroup) :
    L.uniformization (q + p) = L.uniformization q + L.uniformization p := by
  induction q using QuotientAddGroup.induction_on with
  | _ z =>
    induction p using QuotientAddGroup.induction_on with
    | _ w =>
      rw [← QuotientAddGroup.mk_add]
      exact L.toPoint_add z w

/-- $\varphi$ as a homomorphism of additive groups. -/
def uniformizationHom (L : PeriodPair) :
    (ℂ ⧸ L.lattice.toAddSubgroup) →+ L.weierstrassCurve.toAffine.Point where
  toFun := L.uniformization
  map_zero' := L.uniformization_zero
  map_add' := L.uniformization_add

/-- $\varphi$ is injective. Its kernel is trivial, because a point outside $\Lambda$ maps to an
affine point and never to the point at infinity. -/
theorem uniformization_injective (L : PeriodPair) :
    Function.Injective L.uniformization := by
  rw [show L.uniformization = ⇑L.uniformizationHom from rfl, injective_iff_map_eq_zero]
  intro q hq
  induction q using QuotientAddGroup.induction_on with
  | _ z =>
    rw [QuotientAddGroup.eq_zero_iff, Submodule.mem_toAddSubgroup]
    by_contra hz
    exact WeierstrassCurve.Affine.Point.some_ne_zero _
      (by rwa [show L.uniformizationHom z = L.toPoint z from rfl, toPoint, dif_neg hz] at hq)

/-- $\varphi$ is bijective. -/
theorem uniformization_bijective (L : PeriodPair) :
    Function.Bijective L.uniformization :=
  ⟨L.uniformization_injective, fun P ↦ by
    obtain ⟨z, hz⟩ := L.toPoint_surjective P
    exact ⟨QuotientAddGroup.mk z, hz⟩⟩

/-- **The uniformisation theorem.** $\varphi$ is an isomorphism
$\mathbb{C} / \Lambda \simeq E_\Lambda(\mathbb{C})$ of additive groups. -/
def uniformizationEquiv (L : PeriodPair) :
    (ℂ ⧸ L.lattice.toAddSubgroup) ≃+ L.weierstrassCurve.toAffine.Point :=
  AddEquiv.ofBijective L.uniformizationHom L.uniformization_bijective

/- ## The converse: a lattice for a given curve -/

/-- **Existence of the period lattice.** For $4 A^3 + 27 B^2 \neq 0$ there is a lattice with
$g_2 = -4A$ and $g_3 = -4B$. Surjectivity of the modular $j$-function gives a $\tau$ with
$j(\tau) = j(E)$, and a homothety of $\mathbb{Z} + \mathbb{Z}\tau$ then matches the invariants,
since a homothety by $\alpha$ scales $g_n$ by $\alpha^{-n}$. -/
theorem exists_g₂_g₃ {A B : ℂ} (h : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) :
    ∃ L : PeriodPair, L.g₂ = -4 * A ∧ L.g₃ = -4 * B := by sorry

/-- A period lattice for $y^2 = x^3 + A x + B$, chosen using `PeriodPair.exists_g₂_g₃`. Any two
choices have the same lattice, since a period lattice is determined by $g_2$ and $g_3$. -/
def ofCoeffs {A B : ℂ} (h : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) : PeriodPair :=
  (exists_g₂_g₃ h).choose

/- ## Real lattices and the real period -/

/-- The conjugate of a period lattice, whose lattice is the complex conjugate of $\Lambda$. -/
def conjugate (L : PeriodPair) : PeriodPair where
  ω₁ := conj L.ω₁
  ω₂ := conj L.ω₂
  indep := by
    refine LinearIndependent.pair_iff.mpr fun s t hst =>
      LinearIndependent.pair_iff.mp L.indep s t ?_
    have h := congrArg (starRingEnd ℂ) hst
    simpa [Complex.real_smul] using h

/-- A period lattice is *real* if it is stable under complex conjugation. -/
def IsReal (L : PeriodPair) : Prop := L.conjugate.lattice = L.lattice

/-- A lattice is real if and only if $g_2$ and $g_3$ are real. The reverse direction uses that a
period lattice is determined by $g_2$ and $g_3$. -/
theorem isReal_iff_exists_real (L : PeriodPair) :
    L.IsReal ↔ (∃ r : ℝ, L.g₂ = r) ∧ ∃ r : ℝ, L.g₃ = r := by sorry

/-- A real lattice meets $\mathbb{R}$ in a subgroup with a least positive element. That subgroup
is closed because $\Lambda$ is, and nonzero because $l + \overline{l} \in \Lambda$ for
$l \in \Lambda$. A nonzero subgroup of $\mathbb{R}$ with no least positive element is dense by
`AddSubgroup.dense_of_no_min`, and a closed dense subgroup is all of $\mathbb{R}$, which the
discrete $\Lambda$ does not contain. -/
theorem exists_isLeast_pos_real (L : PeriodPair) (hL : L.IsReal) :
    ∃ Ω : ℝ, IsLeast {x : ℝ | (x : ℂ) ∈ L.lattice ∧ 0 < x} Ω := by sorry

/-- The least positive real element of a real lattice. -/
def realPeriod (L : PeriodPair) (hL : L.IsReal) : ℝ :=
  (L.exists_isLeast_pos_real hL).choose

end PeriodPair

namespace WeierstrassCurve

/- ## The period lattice and the real period of a Weierstrass curve -/

/-- The short model $y^2 = x^3 + A x + B$ of an elliptic curve, with $A = -\frac{c_4}{48}$ and
$B = -\frac{c_6}{864}$, is nondegenerate: $4 A^3 + 27 B^2 = -\frac{\Delta}{16}$, by the relation
$1728 \Delta = c_4^3 - c_6^2$. -/
theorem shortModel_discr_ne_zero {F : Type*} [Field F] [CharZero F] (W : WeierstrassCurve F)
    [W.IsElliptic] : 4 * (-W.c₄ / 48) ^ 3 + 27 * (-W.c₆ / 864) ^ 2 ≠ 0 := by
  have hΔ : W.Δ ≠ 0 := by rw [← W.coe_Δ']; exact W.Δ'.ne_zero
  intro h
  exact hΔ (by linear_combination (-16) * h + (1 / 1728) * W.c_relation)

/-- The period lattice of a Weierstrass curve over $\mathbb{C}$, short or long: the lattice with
$g_2 = \frac{c_4}{12}$ and $g_3 = \frac{c_6}{216}$. -/
def periodPair (W : WeierstrassCurve ℂ) [W.IsElliptic] : PeriodPair :=
  PeriodPair.ofCoeffs W.shortModel_discr_ne_zero

/-- The period lattice of a curve with real coefficients is real, since $c_4$ and $c_6$ are. -/
theorem periodPair_map_isReal (W : WeierstrassCurve ℝ) [W.IsElliptic] :
    (W.map Complex.ofRealHom).periodPair.IsReal := by
  obtain ⟨h₂, h₃⟩ :=
    (PeriodPair.exists_g₂_g₃ (W.map Complex.ofRealHom).shortModel_discr_ne_zero).choose_spec
  rw [PeriodPair.isReal_iff_exists_real]
  exact ⟨⟨W.c₄ / 12, h₂.trans (by rw [map_c₄, Complex.ofRealHom_eq_coe]; push_cast; ring)⟩,
    ⟨W.c₆ / 216, h₃.trans (by rw [map_c₆, Complex.ofRealHom_eq_coe]; push_cast; ring)⟩⟩

/-- **The real period** of an elliptic curve over $\mathbb{R}$: the least positive real element
of its period lattice. -/
def realPeriod (W : WeierstrassCurve ℝ) [W.IsElliptic] : ℝ :=
  (W.map Complex.ofRealHom).periodPair.realPeriod W.periodPair_map_isReal

end WeierstrassCurve

end
