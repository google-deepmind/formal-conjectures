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
# Uniform boundedness conjecture for rational points

For a number field $K$ and an integer $g \geq 2$ there is a bound $N(K, g)$ such that every curve
$X$ of genus $g$ over $K$ satisfies $|X(K)| \leq N(K, g)$. This refines Faltings' theorem, which
says that $X(K)$ is finite for each individual curve.

Mathlib has no general theory of algebraic curves and no genus, so curves are described here by
their function fields. The finitely generated field extensions $F / K$ of transcendence degree
$1$ correspond to the regular projective curves over $K$ ([Stacks], Theorem 53.2.6). A number
field has
characteristic zero, and over a field $K$ of characteristic zero such a curve is automatically
smooth, and it is geometrically integral exactly when $K$ is algebraically closed in $F$. Under
this dictionary the closed points of the curve are the places of $F / K$, the degree of a closed
point is the degree of the place, and $X(K)$ is the set of places of degree $1$.
`CurveFunctionField K` bundles a function field with these conditions.

Places are described by their normalised valuations `v : F → ℤᵐ⁰`, in the multiplicative
convention of Mathlib's adic valuations: $v = \exp(-\operatorname{ord})$, so that
$\mathcal{O}_P = \{f \mid v_P(f) \leq 1\}$ and a pole makes $v$ large. `Place.atInfty`, the place
at infinity of the projective line, is worked out as an example, and pins down the direction of
this convention.

The genus is defined here as the least $g$ for which Riemann's inequality
$\ell(D) \geq \deg D + 1 - g$ holds for every divisor $D$; see [Sti2009], Section 1.4.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Uniform_boundedness_conjecture_for_rational_points)
- [Poo] Bjorn Poonen, *Uniform boundedness of rational points*, slides, CNTA XII, 2012,
  https://math.mit.edu/~poonen/slides/uniformboundedness.pdf
- [CHM1997] Lucia Caporaso, Joe Harris, Barry Mazur, *Uniformity of rational points*,
  J. Amer. Math. Soc. 10 (1997), 1-35, https://doi.org/10.1090/S0894-0347-97-00195-1
- [CHM2022] Lucia Caporaso, Joe Harris, Barry Mazur, *Uniformity of rational points: an up-date
  and corrections*, Tunisian J. Math. 4 (2022), 183-201,
  https://doi.org/10.2140/tunis.2022.4.183
- [Pac1997] Patricia L. Pacelli, *Uniform boundedness for rational points*,
  Duke Math. J. 88 (1997), 77-102, https://doi.org/10.1215/S0012-7094-97-08803-7
- [Fal1983] Gerd Faltings, *Endlichkeitssätze für abelsche Varietäten über Zahlkörpern*,
  Invent. Math. 73 (1983), 349-366, https://doi.org/10.1007/BF01388432
- [DGH2021] Vesselin Dimitrov, Ziyang Gao, Philipp Habegger, *Uniformity in Mordell-Lang for
  curves*, Ann. of Math. 194 (2021), 237-298, https://doi.org/10.4007/annals.2021.194.1.4
- [Hab2022] Philipp Habegger, *The number of rational points on a curve of genus at least two*,
  Proc. Int. Cong. Math. 2022, Vol. 3, 1838-1869, https://doi.org/10.4171/ICM2022/79
- [Shi1998] Tetsuji Shioda, *Constructing curves with high rank via symmetry*,
  Amer. J. Math. 120 (1998), no. 3, 551-566, MR1623420
- [Sur2021] Arvind Suresh, *Constructing curves of high rank via composite polynomials*,
  https://arxiv.org/abs/2102.02113
- [Sto] Michael Stoll, *Record genus 2 curve*,
  https://mathe2.uni-bayreuth.de/stoll/recordcurve.html, accessed 2026-09-10
- [Sti2009] Henning Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed.,
  Springer GTM 254, Chapter 1, https://doi.org/10.1007/978-3-540-76878-4
- [Stacks] The Stacks Project, Theorem 53.2.6, https://stacks.math.columbia.edu/tag/0BY1
-/

namespace UniformBoundedness

open Module (finrank)
open scoped WithZero
open WithZero (exp)

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

/-- A place of the field extension $F / K$, presented by its normalised valuation: a surjective
valuation `v : F → ℤᵐ⁰` that is trivial on `K`. Surjectivity is the usual normalisation
$v(F^\times) = \mathbb{Z}$; it also forces $v$ to be non-trivial. Every place of $F / K$ has
exactly one normalised valuation, and a valuation is recovered from its valuation ring, so this
is a faithful description of the set of places. See [Sti2009], Section 1.1. -/
structure Place where
  /-- The normalised valuation of the place. -/
  v : Valuation F ℤᵐ⁰
  /-- The valuation is normalised: its value group is all of `ℤ`. -/
  surjective : Function.Surjective v
  /-- The valuation is trivial on `K`. -/
  isTrivialOn : v.IsTrivialOn K

attribute [instance] Place.isTrivialOn

namespace Place

variable {K F}

/-- A place is determined by its normalised valuation. -/
@[ext, category API, AMS 12]
theorem ext {P Q : Place K F} (h : P.v = Q.v) : P = Q := by
  cases P; cases Q; subst h; rfl

/-- The valuation ring $\mathcal{O}_P = \{f \in F \mid v_P(f) \leq 1\}$ of a place `P`. -/
def integers (P : Place K F) : ValuationSubring F := P.v.valuationSubring

/-- Membership in the valuation ring of a place, unfolded. -/
@[category API, AMS 12]
theorem mem_integers {P : Place K F} {f : F} : f ∈ P.integers ↔ P.v f ≤ 1 := Iff.rfl

/-- A place is a non-trivial valuation, so its valuation ring is a proper subring of `F`. -/
@[category test, AMS 12]
theorem integers_ne_top (P : Place K F) : P.integers ≠ ⊤ := by
  obtain ⟨f, hf⟩ := P.surjective (exp 1)
  intro h
  have hmem : P.v f ≤ 1 := mem_integers.1 (h ▸ ValuationSubring.mem_top f)
  rw [hf, ← WithZero.exp_zero, WithZero.exp_le_exp] at hmem
  norm_num at hmem

/-- The structure map from `K` to the valuation ring of a place of `F / K`. -/
def toIntegers (P : Place K F) : K →+* P.integers :=
  (algebraMap K F).codRestrict _ fun a => Valuation.IsTrivialOn.valuation_algebraMap_le_one P.v a

instance (P : Place K F) : Algebra K P.integers := P.toIntegers.toAlgebra

/-- The residue field $\mathcal{O}_P / \mathfrak{m}_P$ of a place. It is a `K`-vector space
through `Place.toIntegers`. -/
abbrev residueField (P : Place K F) : Type _ := IsLocalRing.ResidueField P.integers

/-- The degree $\deg P = [\mathcal{O}_P / \mathfrak{m}_P : K]$ of a place. It is finite and
positive for every place of a function field of one variable. See [Sti2009], Section 1.1. -/
noncomputable def degree (P : Place K F) : ℕ := finrank K P.residueField

/-- A place has degree one exactly when its residue field is `K`, that is, when it is a
`K`-rational point of the curve. -/
@[category API, AMS 12]
theorem degree_eq_one_iff {P : Place K F} :
    P.degree = 1 ↔ Function.Bijective (algebraMap K P.residueField) :=
  Algebra.finrank_eq_one_iff_bijective_algebraMap

/-- The place at infinity of the projective line over `K`, whose function field is `K(t)`. It is
given by `v(f) = exp (deg (num f) - deg (denom f))`, so that `t`, which has a pole at infinity,
has valuation `exp 1 > 1`. This is a worked example of a genuine geometric place. -/
noncomputable def atInfty (K : Type*) [Field K] [DecidableEq (RatFunc K)] :
    Place K (RatFunc K) where
  v := RatFunc.inftyValuation K
  surjective y := by
    induction y using WithZero.recZeroCoe with
    | zero => exact ⟨0, by simp [RatFunc.inftyValuation_apply, RatFunc.inftyValuationDef]⟩
    | coe m =>
      refine ⟨RatFunc.X ^ (Multiplicative.toAdd m), ?_⟩
      rw [RatFunc.inftyValuation_apply, ← RatFunc.inftyValuation_apply,
        RatFunc.inftyValuation.X_zpow]
      rfl
  isTrivialOn := inferInstance

/-- The valuation of the place at infinity is Mathlib's `RatFunc.inftyValuation`. -/
@[category API, AMS 12]
theorem atInfty_v (K : Type*) [Field K] [DecidableEq (RatFunc K)] :
    (atInfty K).v = RatFunc.inftyValuation K := rfl

end Place

/-- The `Place` encoding is inhabited by a genuine geometric place: the projective line has the
place at infinity. -/
@[category test, AMS 12]
theorem nonempty_place_ratFunc : Nonempty (Place K (RatFunc K)) := by
  classical exact ⟨Place.atInfty K⟩

/-- `t` has a pole at infinity, so it does not lie in the valuation ring of the place at
infinity. Together with `inv_X_mem_integers_atInfty` this pins down the direction of the
multiplicative valuation convention on a real example. -/
@[category test, AMS 12]
theorem X_notMem_integers_atInfty [DecidableEq (RatFunc K)] :
    (RatFunc.X : RatFunc K) ∉ (Place.atInfty K).integers := by
  rw [Place.mem_integers, Place.atInfty_v, RatFunc.inftyValuation.X, ← WithZero.exp_zero,
    WithZero.exp_le_exp]
  norm_num

/-- `1 / t` vanishes at infinity, so it does lie in the valuation ring of the place at
infinity. -/
@[category test, AMS 12]
theorem inv_X_mem_integers_atInfty [DecidableEq (RatFunc K)] :
    (RatFunc.X : RatFunc K)⁻¹ ∈ (Place.atInfty K).integers := by
  rw [Place.mem_integers, show (RatFunc.X : RatFunc K)⁻¹ = 1 / RatFunc.X from (one_div _).symm,
    Place.atInfty_v, RatFunc.inftyValuation.X_inv, ← WithZero.exp_zero, WithZero.exp_le_exp]
  norm_num

/-- A trivial extension has no places: a valuation trivial on `K` is then trivial everywhere, so
it cannot be surjective. -/
@[category test, AMS 12]
theorem isEmpty_place_self : IsEmpty (Place K K) := by
  refine ⟨fun P => ?_⟩
  obtain ⟨f, hf⟩ := P.surjective (exp 1)
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [map_zero] at hf
    exact WithZero.exp_ne_zero hf.symm
  have h1 := Valuation.IsTrivialOn.eq_one (A := K) (v := P.v) f hf0
  rw [Algebra.algebraMap_self_apply, hf, ← WithZero.exp_zero] at h1
  exact one_ne_zero (WithZero.exp_injective h1)

/-- A divisor of $F / K$: a finitely supported formal `ℤ`-linear combination of places.
See [Sti2009], Section 1.4. -/
abbrev Divisor : Type _ := Place K F →₀ ℤ

variable {K F}

/-- The degree $\sum_P n_P \deg P$ of a divisor. -/
noncomputable def Divisor.degree (D : Divisor K F) : ℤ := D.sum fun P n => n * P.degree

/-- The Riemann-Roch space
$L(D) = \{f \in F \mid \operatorname{ord}_P(f) \geq -D(P) \text{ for every place } P\}$ of a
divisor `D`. In the multiplicative convention $v_P = \exp(-\operatorname{ord}_P)$ the condition
reads $v_P(f) \leq \exp(D(P))$. See [Sti2009], Section 1.4. -/
def riemannRochSpace (D : Divisor K F) : Submodule K F where
  carrier := {f | ∀ P : Place K F, P.v f ≤ exp (D P)}
  add_mem' hf hg P := P.v.map_add_le (hf P) (hg P)
  zero_mem' P := by simp
  smul_mem' a f hf P := by
    rw [Algebra.smul_def, map_mul]
    exact le_trans (mul_le_of_le_one_left'
      (Valuation.IsTrivialOn.valuation_algebraMap_le_one P.v a)) (hf P)

/-- Membership in a Riemann-Roch space, unfolded. -/
@[category API, AMS 12]
theorem mem_riemannRochSpace {D : Divisor K F} {f : F} :
    f ∈ riemannRochSpace D ↔ ∀ P : Place K F, P.v f ≤ exp (D P) := Iff.rfl

/-- `L(0)` contains the constants, because a constant function has no poles. -/
@[category test, AMS 12]
theorem algebraMap_mem_riemannRochSpace_zero (a : K) :
    algebraMap K F a ∈ riemannRochSpace (0 : Divisor K F) := fun P => by
  simp

/-- Allowing more poles gives a bigger Riemann-Roch space. This fixes the sign convention: with
`D` and `-D` exchanged the Riemann-Roch space would be antitone instead. -/
@[category test, AMS 12]
theorem riemannRochSpace_mono {D D' : Divisor K F} (h : D ≤ D') :
    riemannRochSpace D ≤ riemannRochSpace D' := fun _ hf P =>
  (hf P).trans (WithZero.exp_le_exp.2 (h P))

variable (K F)

/-- The genus of $F / K$: the least `g` for which Riemann's inequality
$\ell(D) \geq \deg D + 1 - g$ holds for every divisor `D`. Equivalently
$g = \max_D (\deg D - \ell(D) + 1)$, which is the definition in [Sti2009], Section 1.4.

This is the honest genus only for a function field of one variable, and `CurveFunctionField`
below is the intended domain. On an arbitrary extension it returns the junk value `sInf ∅ = 0`
whenever no `g` satisfies the inequality, which is also what would happen if the Riemann-Roch
spaces were infinite-dimensional, since `finrank` is `0` on those. Riemann's inequality,
`riemann_inequality`, is what rules this out on a genuine function field. -/
noncomputable def genus : ℕ :=
  sInf {g : ℕ | ∀ D : Divisor K F,
    D.degree + 1 - (g : ℤ) ≤ (finrank K (riemannRochSpace D) : ℤ)}

/-- A trivial extension has genus `0`: it has no places, so its only divisor is `0`, and
`L(0) = K`. This exercises `genus` end to end, through divisors, degrees and Riemann-Roch spaces.
It does not by itself distinguish `genus` from the junk value `sInf ∅ = 0`; only
`riemann_inequality` does that, by asserting that the defining set is non-empty. -/
@[category test, AMS 12]
theorem genus_self : genus K K = 0 := by
  have hempty := isEmpty_place_self K
  refine Nat.sInf_eq_zero.2 (Or.inl fun D => ?_)
  have h1 : D.degree = 0 := by
    rw [Divisor.degree, Finsupp.sum, Finset.eq_empty_of_isEmpty D.support, Finset.sum_empty]
  have h2 : riemannRochSpace D = ⊤ := by
    ext f
    simp only [mem_riemannRochSpace, Submodule.mem_top, iff_true]
    exact fun P => hempty.elim P
  rw [h1, h2]
  simp

/-- `F` is the function field of a smooth projective geometrically integral curve over `K`, in
the sense of the dictionary recalled in the module docstring: `F / K` is a finitely generated
field extension of transcendence degree `1` in which `K` is algebraically closed. Over a general
field this describes the regular projective model; it is smooth and geometrically integral when
`K` is perfect, in particular whenever `K` is a number field. -/
structure IsCurveFunctionField : Prop where
  /-- `F / K` is a finitely generated field extension. -/
  essFiniteType : Algebra.EssFiniteType K F
  /-- `F / K` has transcendence degree one. -/
  trdeg : Algebra.trdeg K F = 1
  /-- `K` is algebraically closed in `F`, that is, `K` is the full constant field of `F / K`. -/
  algebraicClosure_eq_bot : algebraicClosure K F = ⊥

/-- The rational function field `K(t)` is the function field of a curve, namely of the projective
line. This exhibits an object satisfying `IsCurveFunctionField`, so the statements below are not
vacuous for want of one. -/
@[category test, AMS 12]
theorem isCurveFunctionField_ratFunc : IsCurveFunctionField K (RatFunc K) where
  essFiniteType :=
    have : Algebra.EssFiniteType (Polynomial K) (RatFunc K) :=
      Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors (Polynomial K))
    Algebra.EssFiniteType.comp K (Polynomial K) (RatFunc K)
  trdeg := by
    have : Algebra.IsAlgebraic (Polynomial K) (RatFunc K) :=
      IsLocalization.isAlgebraic _ (nonZeroDivisors (Polynomial K))
    have h := trdeg_add_eq (A := RatFunc K) K (Polynomial K)
    rw [Polynomial.trdeg_of_isDomain, trdeg_eq_zero, add_zero] at h
    exact h.symm
  algebraicClosure_eq_bot := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨c, rfl⟩ : ∃ c, x = RatFunc.C c := by
      by_contra h
      exact RatFunc.transcendental_of_ne_C x h (mem_algebraicClosure_iff.1 hx)
    exact ⟨c, rfl⟩

/-- A curve over `K`, presented by its function field. Bundling `IsCurveFunctionField` with the
field keeps `genus` and `rationalPlaces` away from extensions on which they would return junk
values, and lets the conjecture quantify over curves rather than over carrier types. -/
structure CurveFunctionField.{u} (K : Type u) [Field K] where
  -- A function field of one variable over `K : Type u` is finitely generated over `K`, so it has
  -- a presentation as a localisation of a quotient of `MvPolynomial (Fin n) K`. We therefore lose
  -- no generality by taking `carrier : Type u`, and this keeps the bound `N` in
  -- `uniform_boundedness` from depending on a universe parameter.
  /-- The function field of the curve. -/
  carrier : Type u
  [field : Field carrier]
  [algebra : Algebra K carrier]
  /-- The carrier really is the function field of a curve. -/
  isCurveFunctionField : IsCurveFunctionField K carrier

attribute [instance] CurveFunctionField.field CurveFunctionField.algebra

/-- The projective line over `K`, presented by its function field `K(t)`. -/
noncomputable def CurveFunctionField.projectiveLine : CurveFunctionField K where
  carrier := RatFunc K
  isCurveFunctionField := isCurveFunctionField_ratFunc K

/-- Curves exist: the projective line is one. This rules out `CurveFunctionField K` being empty.
It does not witness a curve of genus at least `2`, which current Mathlib cannot construct, so the
satisfiability of `C.genus = g` for `2 ≤ g` is still not formally established here. -/
@[category test, AMS 12]
theorem nonempty_curveFunctionField : Nonempty (CurveFunctionField K) :=
  ⟨CurveFunctionField.projectiveLine K⟩

variable {K}

/-- The genus of a curve. -/
noncomputable def CurveFunctionField.genus (C : CurveFunctionField K) : ℕ :=
  UniformBoundedness.genus K C.carrier

/-- The rational points of a curve: the places of its function field of degree `1`. -/
def CurveFunctionField.rationalPlaces (C : CurveFunctionField K) : Set (Place K C.carrier) :=
  {P | P.degree = 1}

/-- The rational points of a curve are its places of degree one. -/
@[category API, AMS 12]
theorem CurveFunctionField.mem_rationalPlaces {C : CurveFunctionField K}
    {P : Place K C.carrier} : P ∈ C.rationalPlaces ↔ P.degree = 1 := Iff.rfl

/-- **Riemann's theorem**, also known as Riemann's inequality:
$\ell(D) \geq \deg D + 1 - g$ for every divisor `D` of a function
field of one variable, where `g` is the genus. See [Sti2009], Section 1.4. -/
@[category textbook, AMS 14]
theorem riemann_inequality (C : CurveFunctionField K) (D : Divisor K C.carrier) :
    D.degree + 1 - (C.genus : ℤ) ≤ (finrank K (riemannRochSpace D) : ℤ) := by
  sorry

/-- The **Riemann-Roch theorem** in the range where the canonical divisor contributes nothing:
$\ell(D) = \deg D + 1 - g$ whenever $\deg D > 2g - 2$. Since a function field of one variable has
divisors of arbitrarily large degree, this pins `genus` down to the usual genus. See [Sti2009],
Section 1.5. -/
@[category textbook, AMS 14]
theorem riemann_roch_of_large_degree (C : CurveFunctionField K) (D : Divisor K C.carrier)
    (hD : 2 * (C.genus : ℤ) - 2 < D.degree) :
    (finrank K (riemannRochSpace D) : ℤ) = D.degree + 1 - C.genus := by
  sorry

/-- **Faltings' theorem**, formerly the Mordell conjecture [Fal1983]: a curve of genus at least
`2` over a number field has finitely many rational points. -/
@[category research solved, AMS 11 14]
theorem finite_rationalPlaces (K : Type) [Field K] [NumberField K] (C : CurveFunctionField K)
    (hg : 2 ≤ C.genus) : C.rationalPlaces.Finite := by
  sorry

/-- **The uniform boundedness conjecture for rational points** [CHM1997]: for a number field `K`
and an integer `g ≥ 2` there is a bound `N(K, g)` such that every curve of genus `g` over `K` has
at most `N(K, g)` rational points.

Caporaso, Harris and Mazur proved that this follows from the weak Lang conjecture [CHM1997]; see
[CHM2022] for corrections to that argument. Answering a question of Mazur, Dimitrov, Gao and
Habegger proved the bound `#X(K) ≤ c'(g, d) * c(g, d) ^ r`, where `d` is the degree of `K` and
`r` is the Mordell-Weil rank of the Jacobian of `X` [DGH2021]; see [Hab2022] for a survey. -/
@[category research open, AMS 11 12 14]
theorem uniform_boundedness (K : Type) [Field K] [NumberField K] (g : ℕ) (hg : 2 ≤ g) :
    ∃ N : ℕ, ∀ C : CurveFunctionField K, C.genus = g → C.rationalPlaces.encard ≤ N := by
  sorry

/-- A strengthening of `uniform_boundedness` in which the bound depends only on the genus `g` and
on the degree `d` of the number field, not on the number field itself. Pacelli proved that this
too follows from the weak Lang conjecture [Pac1997]. -/
@[category research open, AMS 11 12 14]
theorem uniform_boundedness.variants.uniform_over_number_fields (d g : ℕ) (hg : 2 ≤ g) :
    ∃ N : ℕ, ∀ (K : Type) [Field K] [NumberField K], finrank ℚ K ≤ d →
      ∀ C : CurveFunctionField K, C.genus = g → C.rationalPlaces.encard ≤ N := by
  sorry

/-- The hypothesis `2 ≤ g` in `uniform_boundedness` excludes the two genera for which the number
of rational points is already unbounded: the projective line, with function field `K(t)`, has
infinitely many `K`-rational points, and every number field carries an elliptic curve of positive
Mordell-Weil rank, obtained by base change from one over `ℚ`. -/
@[category textbook, AMS 11 14]
theorem not_uniform_boundedness_of_genus_le_one (K : Type) [Field K] [NumberField K] (g : ℕ)
    (hg : g ≤ 1) :
    ¬ ∃ N : ℕ, ∀ C : CurveFunctionField K, C.genus = g → C.rationalPlaces.encard ≤ N := by
  sorry

/-- Mestre's construction, refined and generalised by Shioda [Shi1998], gives for every `g ≥ 2` a
curve of genus `g` over `ℚ` with at least `8g + 16` rational points, so any bound `N(ℚ, g)` as in
`uniform_boundedness` satisfies `8g + 16 ≤ N(ℚ, g)`. Mestre's own construction gives `8g + 12`;
the refinement to `8g + 16` is Shioda's. See [Sur2021], Section 1, which surveys both, and which
states the stronger conclusion that infinitely many pairwise non-isomorphic curves of genus `g`
over `ℚ` have at least `8g + 16` rational points. [Poo] and [Hab2022] instead credit `8g + 16` to
Mestre without citing a paper. -/
@[category research solved, AMS 11 14]
theorem mestre_shioda_lower_bound (g : ℕ) (hg : 2 ≤ g) :
    ∃ C : CurveFunctionField ℚ, C.genus = g ∧ 8 * g + 16 ≤ C.rationalPlaces.encard := by
  sorry

/-- Stoll found a curve of genus `2` over `ℚ` with at least `642` rational points, in a family
constructed by Elkies, so any bound `N(ℚ, 2)` as in `uniform_boundedness` satisfies
`642 ≤ N(ℚ, 2)`. See [Hab2022], Section 1, and [Poo]. [Sto] records that this was superseded in
2026 by a genus `2` curve with at least `648` rational points; `642` is kept here as the figure
in the published sources. -/
@[category research solved, AMS 11 14]
theorem stoll_lower_bound :
    ∃ C : CurveFunctionField ℚ, C.genus = 2 ∧ 642 ≤ C.rationalPlaces.encard := by
  sorry

end UniformBoundedness
