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
# The Lang–Trotter conjecture

*References:*
- [WX21] Daqing Wan and Ping Xi, *Lang–Trotter conjecture for CM elliptic curves*,
  Conjecture 1.2, [arxiv/2109.14256](https://arxiv.org/abs/2109.14256)
- [LT76] Serge Lang and Hale Trotter, *Frobenius distributions in $\mathrm{GL}_2$-extensions*,
  Lecture Notes in Mathematics 504, Springer, 1976, https://doi.org/10.1007/BFb0082087
- [Jo09] Nathan Jones, *Averages of elliptic curve constants*,
  Math. Ann. 345 (2009), 685–710, https://doi.org/10.1007/s00208-009-0373-1
- [De41] Max Deuring, *Die Typen der Multiplikatorenringe elliptischer Funktionenkörper*,
  Abh. Math. Sem. Hamburg 14 (1941), 197–272, https://doi.org/10.1007/BF02940746
- [Se72] Jean-Pierre Serre, *Propriétés galoisiennes des points d'ordre fini des courbes
  elliptiques*, Invent. Math. 15 (1972), 259–331, https://doi.org/10.1007/BF01405086
- [Ka09] Nicholas M. Katz, *Lang–Trotter revisited*, Bull. Amer. Math. Soc. 46 (2009), 413–457,
  https://doi.org/10.1090/S0273-0979-09-01257-9
- [LR22] Álvaro Lozano-Robledo, *Galois representations attached to elliptic curves with complex
  multiplication*, Algebra Number Theory 16 (2022), 777–837,
  https://doi.org/10.2140/ant.2022.16.777
- [Ra23] Anwesh Ray, *On the constants of the Lang–Trotter conjecture for CM elliptic curves*,
  [arxiv/2309.09938](https://arxiv.org/abs/2309.09938)
-/

namespace Arxiv.«2109.14256»

open Filter Topology WeierstrassCurve

/-- The trace of Frobenius $a_p(E)$ at a prime $p$ of an elliptic curve $E$ over $\mathbb{Q}$.

It is defined by $|E(\mathbb{F}_p)| = p + 1 - a_p(E)$, where $E(\mathbb{F}_p)$ is the group of
points of the reduction at $p$ of a minimal Weierstrass model of $E$ over $\mathbb{Z}_p$. This
is the same recipe that `WeierstrassCurve.localPolynomial` uses. The value is only meaningful
at primes of good reduction. -/
noncomputable def trace (E : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime] : ℤ :=
  (p : ℤ) + 1 - Nat.card
    (((E.baseChange ℚ_[p]).minimal ℤ_[p]).reduction ℤ_[p]).toAffine.Point

/-- A prime $p$ is *good* for $E$ if $E$ has good reduction at $p$, i.e. if $p \nmid N_E$. -/
def GoodPrime (E : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime] : Prop :=
  ((E.baseChange ℚ_[p]).minimal ℤ_[p]).HasGoodReduction ℤ_[p]

/-- The Lang–Trotter counting function
$$\pi_{E,r}(x) = |\{p \leq x : a_p(E) = r,\ p \nmid N_E\}|.$$ -/
noncomputable def primeCount (E : WeierstrassCurve ℚ) (r : ℤ) (x : ℝ) : ℕ :=
  Nat.card {p : Nat.Primes | letI := Fact.mk p.2
    (p : ℝ) ≤ x ∧ GoodPrime E p ∧ trace E p = r}

/-- An elliptic curve over $\mathbb{Q}$ has *complex multiplication* if and only if its
$j$-invariant is one of the thirteen $j$-invariants of CM elliptic curves over $\mathbb{Q}$,
corresponding to the imaginary quadratic orders of class number one. -/
def HasCM (E : WeierstrassCurve ℚ) [E.IsElliptic] : Prop :=
  E.j ∈ ({0, 1728, -3375, 8000, 54000, 287496, -32768, -884736, 16581375, -12288000,
    -884736000, -147197952000, -262537412640768000} : Set ℚ)

/-- **The Lang–Trotter conjecture.** Let $E$ be an elliptic curve over $\mathbb{Q}$ and let $r$
be an integer, with $r \neq 0$ if $E$ has complex multiplication. Then
$$\pi_{E,r}(x) \sim c_{E,r} \frac{\sqrt{x}}{\log x}$$
for a constant $c_{E,r} \geq 0$ that can be described in terms of the image of the associated
Galois representation. See [LT76] and Conjecture 1.2 of [WX21].

If $c_{E,r} = 0$, the asymptotic formula is interpreted as saying that there are only finitely
many primes $p$ with $a_p(E) = r$; the limit formulation below covers both cases. The case
$r = 0$ of a CM curve is excluded because then $\pi_{E,0}(x) \sim x / (2 \log x)$, by a
classical result of Deuring [De41].

The constant $c_{E,r}$ is left existentially quantified here because no closed form for it is
available in general; see the note below on its conjectural description. -/
@[category research open, AMS 11 14]
theorem lang_trotter (E : WeierstrassCurve ℚ) [E.IsElliptic] (r : ℤ)
    (hr : HasCM E → r ≠ 0) :
    ∃ c : ℝ, 0 ≤ c ∧
      Tendsto (fun x : ℝ ↦ primeCount E r x * Real.log x / Real.sqrt x) atTop (𝓝 c) := by
  sorry

/-
### The Lang–Trotter constant

The constant $c_{E,r}$ is not given by an explicit formula: it is described in terms of the
image of the Galois representation on the torsion of $E$, and [WX21] stresses that even this
description is hard to evaluate for a given pair $(E, r)$.

For a subgroup $G \leq \mathrm{GL}_2(\mathbb{Z}/n\mathbb{Z})$ write
$G_r := \{g \in G : \mathrm{tr}\, g \equiv r \pmod n\}$. Let $E$ have CM by the imaginary
quadratic field $K = \mathbb{Q}(\sqrt{-D})$ with $D \geq 1$ squarefree, and let $R_D$ be the
relevant order, so that the Galois action on torsion gives
$\rho_E : \mathrm{Gal}(\overline{\mathbb{Q}}/K) \to \mathrm{GL}_1(R_D)$, whose image has finite
index by [Se72, Section 4.5]. Let $m_E$ be the least $m_0 \geq 1$ such that
$$\mathrm{Gal}(K(E[m])/K) = \pi^{-1}(\mathrm{Gal}(K(E[(m, m_0)])/K))$$
for every $m \geq 1$, where $\pi : (R_D/mR_D)^\times \to (R_D/(m, m_0)R_D)^\times$ is the
canonical projection, taken divisible by $4p$ for every prime $p$ ramified in $R_D$. Viewing
$\mathrm{GL}_1(R_D/mR_D)$ inside $\mathrm{GL}_2(\mathbb{Z}/m\mathbb{Z})$ via a
$\mathbb{Z}/m\mathbb{Z}$-basis of $R_D/mR_D$, Jones [Jo09, Section 2.2] interpreted the
constant as
$$
  c_{E,r} = \frac{m_E}{2} \cdot
    \frac{|\mathrm{Gal}(K(E[m_E])/K)_r|}{|\mathrm{Gal}(K(E[m_E])/K)|} \cdot
    \prod_{p \mid r,\; p \nmid m_E} \left(1 - \frac{\left(\frac{-D}{p}\right)}{p}\right)^{-1}
    \prod_{p \nmid r m_E}
      \left(1 - \frac{\left(\frac{-D}{p}\right)}
        {(p - 1)\left(p - \left(\frac{-D}{p}\right)\right)}\right),
$$
where $\left(\frac{-D}{p}\right)$ is the Legendre symbol; see equation (1.3) and Section 7.4
of [WX21].

In particular $c_{E,r} > 0$ if and only if the Galois image contains an element of trace $r$,
so $c_{E,r} = 0$ exactly when there is a congruence obstruction, discussed in general in
[Ka09]. For example $c_{E,2} > 0$ always, since the identity matrix has trace $2$.

The Galois image in the CM case is classified in [LR22], which makes an explicit description
of $c_{E,r}$ possible; [Ra23] carries this out for twenty CM curves. The main point of [WX21]
is to replace the description above by an analytically defined, completely explicit constant
$\mathfrak{c}_{E,r}$, and to conjecture that $c_{E,r} = \mathfrak{c}_{E,r}$ (Conjecture 1.5,
the Comparison Conjecture).
-/

end Arxiv.«2109.14256»
