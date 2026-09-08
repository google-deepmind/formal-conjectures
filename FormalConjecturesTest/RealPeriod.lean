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

import FormalConjecturesTest.RealPeriod.Existence
import FormalConjecturesTest.RealPeriod.Conjugation
import FormalConjecturesTest.RealComponents

/-!
# The real period of an elliptic curve

Every elliptic curve $E$ over $\mathbb{C}$ is $\mathbb{C} / \Lambda$ for a lattice $\Lambda$,
determined by $E$ through its invariants: $g_2(\Lambda) = \frac{c_4}{12}$ and
$g_3(\Lambda) = \frac{c_6}{216}$. Under the isomorphism $z \mapsto (\wp(z), \frac{1}{2} \wp'(z))$
the invariant differential $\frac{dx}{2y + a_1 x + a_3}$ pulls back to $dz$, so the elements of
$\Lambda$ are the periods of that differential. This is why $\Lambda$ is called the period
lattice of $E$.

If $E$ is defined over $\mathbb{R}$ then $\Lambda$ is stable under complex conjugation, and
$\Lambda \cap \mathbb{R} = \mathbb{Z} \Omega_0$ for a unique $\Omega_0 > 0$, the least positive
real period, which is the length of the identity component of $E(\mathbb{R})$. The *real period*
of $E$, the one in the Birch and Swinnerton-Dyer conjecture, is $\Omega_0$ or $2\Omega_0$
according as the discriminant is negative or positive: $\Omega_0$ times the number of connected
components of $E(\mathbb{R})$, `WeierstrassCurve.nrRealComponents`.

This file defines the period lattice of a Weierstrass curve over $\mathbb{C}$,
`WeierstrassCurve.periodPair`, the least positive real period of an elliptic curve over
$\mathbb{R}$, `WeierstrassCurve.leastRealPeriod`, and the real period `WeierstrassCurve.realPeriod`.
They rest on three classical facts:

* `PeriodPair.exists_g₂_g₃`: a lattice with any prescribed nondegenerate invariants exists.
  Proved in `FormalConjecturesTest.RealPeriod.Existence`, from surjectivity of the modular
  $j$-function and the nonvanishing of the discriminant of a lattice.
* `PeriodPair.isReal_iff_exists_real`: a lattice is real if and only if its invariants are.
  Proved in `FormalConjecturesTest.RealPeriod.Conjugation`, from the uniqueness of the lattice
  with given invariants.
* `PeriodPair.exists_isLeast_pos_real`: a real lattice has a least positive real element,
  packaged as `PeriodPair.leastRealPeriod` with specification `isLeast_leastRealPeriod`.
  Proved below.

The uniformisation isomorphism is what identifies $\Lambda$ with the periods of the invariant
differential, but the definitions do not depend on it, and it is not included.

*References:*
- Wikipedia, *Weierstrass elliptic function*,
    https://en.wikipedia.org/wiki/Weierstrass_elliptic_function
- Wikipedia, *Birch and Swinnerton-Dyer conjecture*,
    https://en.wikipedia.org/wiki/Birch_and_Swinnerton-Dyer_conjecture
- [Sil2009] Joseph H. Silverman. The Arithmetic of Elliptic Curves, 2nd edition, Chapter VI,
    https://link.springer.com/book/10.1007/978-0-387-09494-6
- [Cre1997] John E. Cremona. Algorithms for Modular Elliptic Curves, 2nd edition, Section 3.7,
    https://johncremona.github.io/book/fulltext/index.html
-/

open scoped ComplexConjugate

noncomputable section

namespace PeriodPair

/- ## A lattice for a given curve -/

/-- A period lattice for $y^2 = x^3 + A x + B$, chosen using `PeriodPair.exists_g₂_g₃`. Any two
choices have the same lattice, by `PeriodPair.lattice_eq_of_g₂_eq_of_g₃_eq`. -/
def ofCoeffs {A B : ℂ} (h : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) : PeriodPair :=
  (exists_g₂_g₃ h).choose

/- ## The real period of a real lattice -/

/-- A real lattice meets $\mathbb{R}$ in a subgroup with a least positive element. That subgroup
is closed because $\Lambda$ is, and nonzero because $\omega + \overline{\omega} = 2
\operatorname{Re} \omega$ lies in $\Lambda$ for $\omega \in \Lambda$, and some period has nonzero
real part. A nonzero subgroup of $\mathbb{R}$ with no least positive element is dense
(`AddSubgroup.dense_of_no_min`), and a closed dense subgroup is all of $\mathbb{R}$, which the
countable $\Lambda$ does not contain. -/
theorem exists_isLeast_pos_real (L : PeriodPair) (hL : L.IsReal) :
    ∃ Ω : ℝ, IsLeast {x : ℝ | (x : ℂ) ∈ L.lattice ∧ 0 < x} Ω := by
  -- The real points of `Λ`, as an additive subgroup of `ℝ`.
  set H : AddSubgroup ℝ := L.lattice.toAddSubgroup.comap (Complex.ofRealHom : ℝ →+ ℂ)
  have hmem : ∀ x : ℝ, x ∈ H ↔ (x : ℂ) ∈ L.lattice := fun x ↦ Iff.rfl
  -- `Λ` is stable under conjugation, so `ω + conj ω = 2 Re ω` lies in `Λ` for `ω ∈ Λ`.
  have hconj : ∀ ω ∈ L.lattice, conj ω ∈ L.lattice := fun ω hω ↦ by
    rw [← hL]
    exact L.mem_conjugate_lattice.mpr (by simpa using hω)
  have hre : ∀ ω ∈ L.lattice, (2 * ω.re : ℝ) ∈ H := fun ω hω ↦ by
    rw [hmem, ← Complex.add_conj]
    exact add_mem hω (hconj ω hω)
  -- Some period has nonzero real part, since `ω₁` and `ω₂` are `ℝ`-linearly independent.
  obtain ⟨ω, hω, hω0⟩ : ∃ ω ∈ L.lattice, ω.re ≠ 0 := by
    by_contra! h
    have h₁ : L.ω₁.re = 0 := h _ L.ω₁_mem_lattice
    have h₂ : L.ω₂.re = 0 := h _ L.ω₂_mem_lattice
    have hlin := (LinearIndependent.pair_iff.mp L.indep) L.ω₂.im (-L.ω₁.im) (by
      apply Complex.ext <;> simp [Complex.real_smul, h₁, h₂]
      ring)
    exact L.ω₁_ne_zero (Complex.ext (by simpa using h₁) (by simpa using hlin.2))
  have hbot : H ≠ ⊥ := by
    intro hb
    have := hre ω hω
    rw [hb, AddSubgroup.mem_bot] at this
    exact hω0 (by linarith)
  -- `H` is closed, so with no least positive element it would be dense, hence all of `ℝ`.
  have hclosed : IsClosed (H : Set ℝ) := L.isClosed_lattice.preimage Complex.continuous_ofReal
  by_contra hno
  have huniv : (H : Set ℝ) = Set.univ :=
    hclosed.closure_eq.symm.trans (H.dense_of_no_min hbot hno).closure_eq
  -- But `Λ` is countable and `ℝ` is not.
  have hΛ : (L.lattice : Set ℂ).Countable := countable_of_Lindelof_of_discrete (X := L.lattice)
  have hcount : (H : Set ℝ).Countable := hΛ.preimage Complex.ofReal_injective
  rw [huniv] at hcount
  exact Cardinal.not_countable_real hcount

/-- The least positive real element of a real lattice. -/
def leastRealPeriod (L : PeriodPair) (hL : L.IsReal) : ℝ :=
  (L.exists_isLeast_pos_real hL).choose

lemma isLeast_leastRealPeriod (L : PeriodPair) (hL : L.IsReal) :
    IsLeast {x : ℝ | (x : ℂ) ∈ L.lattice ∧ 0 < x} (L.leastRealPeriod hL) :=
  (L.exists_isLeast_pos_real hL).choose_spec

lemma leastRealPeriod_pos (L : PeriodPair) (hL : L.IsReal) : 0 < L.leastRealPeriod hL :=
  (L.isLeast_leastRealPeriod hL).1.2

lemma coe_leastRealPeriod_mem_lattice (L : PeriodPair) (hL : L.IsReal) :
    (L.leastRealPeriod hL : ℂ) ∈ L.lattice :=
  (L.isLeast_leastRealPeriod hL).1.1

lemma leastRealPeriod_le (L : PeriodPair) (hL : L.IsReal) {x : ℝ} (hx : (x : ℂ) ∈ L.lattice)
    (h0 : 0 < x) : L.leastRealPeriod hL ≤ x :=
  (L.isLeast_leastRealPeriod hL).2 ⟨hx, h0⟩

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

/-- The least positive real period of an elliptic curve over $\mathbb{R}$: the least positive real
element of its period lattice, the length of the identity component of $E(\mathbb{R})$. -/
def leastRealPeriod (W : WeierstrassCurve ℝ) [W.IsElliptic] : ℝ :=
  (W.map Complex.ofRealHom).periodPair.leastRealPeriod W.periodPair_map_isReal

lemma leastRealPeriod_pos (W : WeierstrassCurve ℝ) [W.IsElliptic] : 0 < W.leastRealPeriod :=
  PeriodPair.leastRealPeriod_pos _ _

/-- **The real period** of an elliptic curve over $\mathbb{R}$: the least positive real period
multiplied by the number of connected components of $E(\mathbb{R})$. This is the real period of the
Birch and Swinnerton-Dyer conjecture. -/
def realPeriod (W : WeierstrassCurve ℝ) [W.IsElliptic] : ℝ :=
  (W.nrRealComponents : ℝ) * W.leastRealPeriod

lemma realPeriod_pos (W : WeierstrassCurve ℝ) [W.IsElliptic] : 0 < W.realPeriod :=
  mul_pos (Nat.cast_pos.mpr W.nrRealComponents_pos) W.leastRealPeriod_pos

lemma realPeriod_of_pos (W : WeierstrassCurve ℝ) [W.IsElliptic] (h : 0 < W.Δ) :
    W.realPeriod = 2 * W.leastRealPeriod := by
  simp [realPeriod, W.nrRealComponents_of_pos h]

lemma realPeriod_of_neg (W : WeierstrassCurve ℝ) [W.IsElliptic] (h : W.Δ < 0) :
    W.realPeriod = W.leastRealPeriod := by
  simp [realPeriod, W.nrRealComponents_of_neg h]

end WeierstrassCurve

end
