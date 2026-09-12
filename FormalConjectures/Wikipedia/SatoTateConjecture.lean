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
import FormalConjectures.Wikipedia.ModularityConjecture

/-!
# Sato–Tate conjecture

The **Sato–Tate conjecture** describes the distribution of the normalized Frobenius traces
$a_p(E)/(2\sqrt{p})$ of a non-CM elliptic curve $E$ over $\mathbb{Q}$, as $p$ ranges over
the primes of good reduction: they equidistribute in $[-1,1]$ with respect to the
**Sato–Tate measure**
$$
\frac{2}{\pi}\sqrt{1-x^2}\,dx.
$$

Originally conjectured independently by Mikio Sato and John Tate around 1960, it is
now a theorem: the case of elliptic curves over totally real fields with nonintegral
$j$-invariant was established through the work of Clozel, Harris, and Taylor [CHT08],
Taylor [Tay08], and Harris, Shepherd-Barron, and Taylor [HST10]. The remaining non-CM
case was settled by Barnet-Lamb, Geraghty, Harris, and Taylor [BGHT11]. In particular,
it holds unconditionally for every non-CM elliptic curve over $\mathbb{Q}$.

We use `ModularityConjecture.WeierstrassCurve.ap`, which agrees with the Frobenius
trace at every prime where the supplied Weierstrass equation has integral
coefficients and nonsingular reduction. Only finitely many primes are exceptional.
Including these primes does not change the limiting density, so the formal
statement averages over all primes below $N$.

The non-CM hypothesis is expressed using the classification of rational CM
$j$-invariants. Complex multiplication here means complex multiplication over
$\overline{\mathbb{Q}}$.

## References

- [CHT08] L. Clozel, M. Harris, R. Taylor, *Automorphy for some $l$-adic lifts of
  automorphic mod $l$ Galois representations*, Publications Mathématiques de l'IHÉS
  108 (2008), 1–181. https://doi.org/10.1007/s10240-008-0016-1
- [Tay08] R. Taylor, *Automorphy for some $l$-adic lifts of automorphic mod $l$
  Galois representations. II*, Publications Mathématiques de l'IHÉS
  108 (2008), 183–239. https://doi.org/10.1007/s10240-008-0015-2
- [HST10] M. Harris, N. Shepherd-Barron, R. Taylor, *A family of Calabi-Yau varieties
  and potential automorphy*, Annals of Mathematics 171 (2010), no. 2, 779–813.
  https://doi.org/10.4007/annals.2010.171.779
- [BGHT11] T. Barnet-Lamb, D. Geraghty, M. Harris, R. Taylor, *A family of Calabi-Yau
  varieties and potential automorphy II*, Publications of the Research Institute
  for Mathematical Sciences 47 (2011), no. 1, 29–98.
  https://doi.org/10.2977/PRIMS/31
- [Wikipedia](https://en.wikipedia.org/wiki/Sato%E2%80%93Tate_conjecture)
-/

namespace SatoTateConjecture

open Real

/-- The thirteen rational CM $j$-invariants, corresponding respectively to the
imaginary quadratic orders of discriminants
$-3,-4,-7,-8,-11,-12,-16,-19,-27,-28,-43,-67,-163$. -/
def cmJInvariants : Finset ℚ :=
  {0, 1728, -3375, 8000, -32768, 54000, 287496, -884736,
    -12288000, 16581375, -884736000, -147197952000, -262537412640768000}

/-- An elliptic curve $E$ over $\mathbb{Q}$ has complex multiplication over
$\overline{\mathbb{Q}}$ if its $j$-invariant belongs to the set of thirteen
rational CM $j$-invariants. -/
def HasCM (E : WeierstrassCurve ℚ) [E.IsElliptic] : Prop :=
  E.j ∈ cmJInvariants

/-- The normalized coefficient $a_p(E)/(2\sqrt{p})$, using the point-counting
definition from `ModularityConjecture`.

At primes where the supplied equation has integral coefficients and nonsingular
reduction, this is the normalized Frobenius trace and lies in $[-1,1]$. -/
noncomputable def normalisedAp
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) : ℝ :=
  (ModularityConjecture.WeierstrassCurve.ap E p : ℝ) /
    (2 * √p)

/-- The cumulative distribution function of the Sato–Tate measure. For
$t \in [-1,1]$, it is given by
$$
F(t) = \frac{t\sqrt{1-t^2}+\arcsin t}{\pi}+\frac{1}{2}.
$$
Mathlib's definitions of `Real.sqrt` and `Real.arcsin` make this expression
equal to $0$ for $t \le -1$ and $1$ for $t \ge 1$. -/
noncomputable def satoTateCDF (t : ℝ) : ℝ :=
  (t * √(1 - t ^ 2) + arcsin t) / π + 1 / 2

/-- For $a \le b$, the mass assigned to $[a,b]$ by the Sato–Tate distribution.
This is a real-valued interval mass, not a `MeasureTheory.Measure` object. -/
noncomputable def satoTateMeasure (a b : ℝ) : ℝ :=
  satoTateCDF b - satoTateCDF a

/-- For $a \le b$, the mass assigned to $[a,b]$ by the Sato–Tate distribution, written in its
usual integral form
$$
\frac{2}{\pi}\int_a^b \sqrt{1-x^2}\,dx.
$$ -/
noncomputable def satoTateIntegral (a b : ℝ) : ℝ :=
  2 / π * ∫ x in a..b, √(1 - x ^ 2)

/-- Sanity check: for $-1 \le a \le b \le 1$, the closed-form interval mass `satoTateMeasure`
agrees with the integral form `satoTateIntegral`. -/
@[category test, AMS 11 14]
theorem satoTateMeasure_eq_satoTateIntegral
    (a b : ℝ) (ha : -1 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    satoTateMeasure a b = satoTateIntegral a b := by
  have hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt satoTateCDF (2 / π * √(1 - x ^ 2)) x := by
    intro x hx
    have hx1 : -1 < x := ha.trans_lt hx.1
    have hx2 : x < 1 := hx.2.trans_le hb
    have hpos : (0 : ℝ) < 1 - x ^ 2 := by nlinarith
    have hsq : HasDerivAt (fun t : ℝ ↦ 1 - t ^ 2) (-(2 * x)) x := by
      simpa using (hasDerivAt_pow 2 x).const_sub 1
    have heq : 1 * √(1 - x ^ 2) + x * (-(2 * x) / (2 * √(1 - x ^ 2))) + 1 / √(1 - x ^ 2) =
        2 * √(1 - x ^ 2) := by
      grind
    have h2 : (2 : ℝ) / π * √(1 - x ^ 2) = (2 * √(1 - x ^ 2)) / π := by ring
    rw [h2, ← heq]
    exact ((((hasDerivAt_id x).mul (hsq.sqrt hpos.ne')).add <|
      hasDerivAt_arcsin hx1.ne' hx2.ne).div_const π).add_const (1 / 2)
  have hint : IntervalIntegrable (fun x : ℝ ↦ 2 / π * √(1 - x ^ 2))
      MeasureTheory.volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab (by
    fun_prop [satoTateCDF]) hderiv hint
  grind [satoTateMeasure, satoTateIntegral, ← intervalIntegral.integral_const_mul]

/-- The number of primes $p < N$ for which the normalized coefficient belongs
to $[a,b]$. -/
noncomputable def primeCountInInterval
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (a b : ℝ) (N : ℕ) : ℕ :=
  ((Nat.primesBelow N).filter
      (fun p : ℕ ↦ a ≤ normalisedAp E p ∧ normalisedAp E p ≤ b)).card

/-- **The Sato–Tate conjecture**: for a non-CM elliptic curve $E$ over $\mathbb{Q}$ and
$-1 \le a \le b \le 1$, the proportion of primes $p < N$ whose normalized coefficient
belongs to $[a,b]$ tends to
$$
\frac{2}{\pi}\int_a^b \sqrt{1-x^2}\,dx
$$
as $N \to \infty$.

The finitely many primes where the supplied equation fails to have integral
coefficients and nonsingular reduction do not affect this limit.

Established through the work of Clozel–Harris–Taylor [CHT08], Taylor [Tay08],
Harris–Shepherd-Barron–Taylor [HST10], and
Barnet-Lamb–Geraghty–Harris–Taylor [BGHT11]. -/
@[category research solved, AMS 11 14]
theorem satoTate_conjecture
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (hCM : ¬ HasCM E)
    (a b : ℝ) (ha : -1 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Filter.Tendsto
      (fun N : ℕ ↦
        (primeCountInInterval E a b N : ℝ) /
          ((Nat.primesBelow N).card : ℝ))
      Filter.atTop
      (nhds (satoTateMeasure a b)) := by
  sorry

end SatoTateConjecture
