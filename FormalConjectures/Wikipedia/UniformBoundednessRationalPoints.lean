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
# Uniform boundedness conjecture for rational points

For a number field $K$ and an integer $g \geq 2$ there is a bound $N(K, g)$ such that every curve
$X$ of genus $g$ over $K$ satisfies $|X(K)| \leq N(K, g)$. This refines Faltings' theorem, which
says that $X(K)$ is finite for each individual curve.

Mathlib has no general theory of algebraic curves and no genus, so curves are described here by
their function fields. The finitely generated field extensions $F / K$ of transcendence degree
$1$ correspond to the regular projective curves over $K$ ([Stacks], Theorem 53.2.6). A number
field has characteristic zero, and over a field $K$ of characteristic zero such a curve is
automatically smooth, and it is geometrically integral exactly when $K$ is algebraically closed
in $F$. Under this dictionary the closed points of the curve are the places of $F / K$, the degree
of a closed point is the degree of the place, and $X(K)$ is the set of places of degree $1$.
`FunctionField.CurveFunctionField K` bundles a function field with these conditions. It and the
other definitions used here are in `FormalConjecturesForMathlib/FieldTheory/FunctionField/`.

Places are described by their normalised valuations `v : F → ℤᵐ⁰`, in the multiplicative
convention of Mathlib's adic valuations: $v = \exp(-\operatorname{ord})$, so that
$\mathcal{O}_P = \{f \mid v_P(f) \leq 1\}$ and a pole makes $v$ large. The place at infinity of
the projective line, `FunctionField.Place.atInfty`, is worked out there as an example. It pins
down the direction of this convention, and it has degree $1$.

The genus is defined as the least $g$ for which Riemann's inequality
$\ell(D) \geq \deg D + 1 - g$ holds for every divisor $D$; see [Sti2009], Section 1.4.
`riemann_inequality` and `riemann_roch_of_large_degree` below record why this is the usual genus.

Mazur's conjecture B, the weaker statement in which the bound may also depend on the Mordell-Weil
rank of the Jacobian and which Dimitrov, Gao and Habegger proved [DGH2021], is not formalised
here, because Mathlib has no Jacobians of curves and hence no Mordell-Weil rank.

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

@[expose] public section

namespace UniformBoundedness

open Module (finrank)
open FunctionField

variable {K : Type*} [Field K]

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
