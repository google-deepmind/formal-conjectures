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

public import FormalConjecturesForMathlib.AlgebraicGeometry.EllipticCurve.PeriodIntegral

@[expose] public section

/-!
# Numerical check of `realPeriodIntegral` against the LMFDB

`WeierstrassCurve.realPeriodIntegral` is a real number defined by an improper integral, so it
cannot be evaluated by `#eval`. This file checks it against an independent source of the same
number: the `ec.q.real_period` column of the LMFDB, for twenty elliptic curves over
$\mathbb{Q}$ spanning Mordell–Weil ranks $0$–$3$, both signs of the discriminant, conductors
from $11$ to $5077$, and torsion of every order from $1$ to $16$ that occurs.

The check is a floating-point one: the definitions of
`FormalConjecturesForMathlib.AlgebraicGeometry.EllipticCurve.PeriodIntegral` are transcribed
into `Float`, the transcription is integrated numerically, and the answer is compared to the
LMFDB's. What it can catch is a wrong *definition* — a missing factor of $2$, the wrong
component of $E(\mathbb{R})$, the wrong convention for the real Tamagawa number $c_\infty$ —
which is exactly the risk that a proof of the lemmas in that file does not address. It is not,
and cannot be, a proof.

## The dictionary

Every declaration of `LMFDBCurve` below transcribes the declaration of the same name, so the
correspondence is by name; what each one does differently in `Float` is this.

* `b₂`, `b₄`, `b₆`, `evalΨ₂Sq` are `WeierstrassCurve.b₂`, `b₄`, `b₆` and `W.Ψ₂Sq.eval` written
  out. The `example`s under *The correspondence with the definitions over `ℝ`* prove that the
  formulas used here are the ones mathlib defines.
* `integrand` is `WeierstrassCurve.realPeriodIntegrand`. Over `ℝ` its junk value where the cubic
  is not positive falls out of `√v = 0` and `0⁻¹ = 0`; in `Float` those same two expressions give
  `1 / 0 = ∞`, so the junk value is an explicit `if`.
* `e₁` is `WeierstrassCurve.e₁`, defined there as a supremum and computed here by the
  trigonometric solution of the cubic followed by Newton.
* `leastRealPeriodIntegral` and `realPeriodIntegral` are the definitions of those names,
  $2\int_{e_1}^\infty$ and $2\int_{\mathbb{R}}$; the latter is computed as the identity component
  plus twice `ovalIntegral`.
* `realPeriod` is not a transcription of anything: it is the LMFDB's number, the one being
  checked against.

## Quadrature

The integrand has an inverse-square-root singularity at each real root of $\Psi_2^2$ and the
domain is unbounded, so the quadrature is double-exponential: `tanhSinh` on a bounded interval
and `expSinh` on $[0, \infty)$, at $2801$ nodes of spacing $1/256$.

Two integrators are run against every curve.

* `LMFDBCurve.realPeriodIntegral` removes the singularities analytically before sampling. On the
  identity component it substitutes $x = e_1 + s^2$ and cancels the factor $s$ against the
  Jacobian: with $\Psi_2^2 = (X - e_1) G$ this makes the integrand $2 / \sqrt{G(e_1 + s^2)}$, and
  $G$ is evaluated from its own coefficients rather than as a quotient. On the oval it
  substitutes $x = \frac{e_2 + e_3}{2} + \frac{e_2 - e_3}{2}\sin\theta$, which likewise cancels
  against $\sqrt{(x - e_2)(x - e_3)}$ and leaves $1 / (2\sqrt{e_1 - x(\theta)})$. It agrees with
  the LMFDB to $10^{-14}$ relative, which is as close as a `Float` gets.
* `LMFDBCurve.naiveRealPeriodIntegral` feeds `LMFDBCurve.integrand` itself to the same quadrature,
  so it exercises the transcription of `realPeriodIntegrand` literally, junk value included. It
  keeps only four to nine digits: next to a root, $4x^3 + b_2x^2 + 2b_4x + b_6$ loses all of its
  significant digits to cancellation — the more so the larger the coefficients — and the value of
  the integral is correspondingly sensitive to the computed $e_1$. That is a defect of the
  arithmetic, not of the definition, so it is checked at a tolerance of $10^{-4}$.

The double-exponential rules also lose accuracy when the cubic is close to having a double root,
that is when $\Delta$ is small next to the coefficients: the quadrature then has a pole just off
the contour. Three of the curves below are mildly so — `57.a1`, whose cubic $4x^3 - 4x^2 - 8x + 9$
comes within $0.55$ of a double root at $x \approx 1.22$, is the worst — and that, rather than the
singularities, is what fixes the node spacing at $1/256$.

## Cross-validation

Agreeing with the LMFDB is evidence about the definition, not about the quadrature, so the
quadrature was checked separately against a closed form. Applying $\int_0^\infty \frac{ds}
{\sqrt{(s^2+a^2)(s^2+b^2)}} = \frac{\pi}{2\,\mathrm{AGM}(a, b)}$ to the substitution above
gives $2\int_{e_1}^\infty \frac{dx}{\sqrt{\Psi_2^2(x)}} = \pi / \mathrm{AGM}(\sqrt{e_1 -
e_3}, \sqrt{e_1 - e_2})$ when the roots are real, and one Gauss descent turns the
complex-conjugate pair into the real arguments $\sqrt{p + 2n}/2$ and $\sqrt{n}$, where
$p = 3e_1 + b_2/4$ and $n = \sqrt{\Psi_2^{2\prime}(e_1)}/2$. On $4000$ random integral curves
the two routes agreed to machine precision. Where they did not, refining the node spacing moved
the quadrature onto the arithmetic-geometric mean rather than away from it, which is both what
identifies the near-degenerate curves above as a defect of the quadrature and how the spacing
was chosen. The same sweep found no curve where $\Delta > 0$ disagreed with $\Psi_2^2$ having
three real roots, which `LMFDBCurve.discSignAgrees` re-checks for each curve below.

## What comes out

`realPeriodIntegral` for each of the twenty curves, beside the LMFDB's `real_period` and the
relative difference in units of $10^{-15}$. This is `report`; `#eval IO.println report`
regenerates it.

```
curve    realPeriodIntegral  LMFDB real_period   err
11.a1    0.253841860855910   0.253841860855911   3.28
11.a2    1.269209304279553   1.269209304279550   2.10
11.a3    6.346046521397755   6.346046521397770   2.38
14.a1    0.660447318688961   0.660447318688961   0.67
14.a3    1.981341956066882   1.981341956066880   1.12
15.a2    1.400603042332601   1.400603042332600   0.63
15.a5    2.801206084665201   2.801206084665200   0.63
19.a2    1.359759733488308   1.359759733488310   1.14
26.b2    4.346757446843395   4.346757446843390   1.02
30.a6    3.351948259241495   3.351948259241500   1.46
37.a1    5.986917292463913   5.986917292463920   1.19
43.a1    5.468689529967589   5.468689529967581   1.46
53.a1    4.687641048878886   4.687641048878880   1.33
54.b2    3.091565549103005   3.091565549103010   1.44
57.a1    5.555504521372506   5.555504521372500   1.12
66.c3    2.383229631224970   2.383229631224970   0.00
210.e6   1.025933010019532   1.025933010019530   2.38
389.a1   4.980425121710102   4.980425121710110   1.61
433.a1   4.214710192998487   4.214710192998480   1.69
5077.a1  4.151687983086932   4.151687983086930   0.43
```

*References:*
- [LMFDB](https://www.lmfdb.org/knowledge/show/ec.q.real_period), knowl `ec.q.real_period`: the
  quantity being checked against, $\Omega = \int_{E(\mathbb{R})} |\omega|$, in the convention
  that includes the real Tamagawa number.
- [ecdata](https://github.com/JohnCremona/ecdata), John Cremona's database, which is the source
  of the LMFDB's elliptic curve pages. The `ainvs`, `rank`, `torsion` and `realPeriod` columns
  below are the `AI`, `R`, `T` and `OM` fields of `allbsd/allbsd.00000-09999`, relabelled by
  `alllabels/alllabels.00000-09999`, retrieved 2026-09-09; `disc` is computed from `ainvs`. The
  `OM` values agree with the LMFDB's `real_period` column, checked through the LMFDB API for
  `11.a2` ($1.2692093042795534216887946168$).
-/

namespace WeierstrassCurve.PeriodIntegralTest

/-! ## The `Float` transcription -/

/-- $\pi$, to the precision of a `Float`. -/
def pi : Float := 3.141592653589793

/-- An elliptic curve over $\mathbb{Q}$ as the LMFDB records it: its label, its `ainvs`, its
Mordell–Weil `rank`, the order of its torsion subgroup, its discriminant, and the real period
`ec.q.real_period` that this file checks `WeierstrassCurve.realPeriodIntegral` against. -/
structure LMFDBCurve where
  /-- The LMFDB label of the curve. -/
  label : String
  /-- The coefficient $a_1$. -/
  a₁ : Float
  /-- The coefficient $a_2$. -/
  a₂ : Float
  /-- The coefficient $a_3$. -/
  a₃ : Float
  /-- The coefficient $a_4$. -/
  a₄ : Float
  /-- The coefficient $a_6$. -/
  a₆ : Float
  /-- The Mordell–Weil rank. -/
  rank : Nat
  /-- The order of the torsion subgroup. -/
  torsion : Nat
  /-- The discriminant $\Delta$. -/
  disc : Float
  /-- The real period, from the `real_period` column of the LMFDB's `ec_mwbsd` table. -/
  realPeriod : Float

namespace LMFDBCurve

variable (C : LMFDBCurve)

/-- `WeierstrassCurve.b₂`. -/
def b₂ : Float := C.a₁ * C.a₁ + 4 * C.a₂

/-- `WeierstrassCurve.b₄`. -/
def b₄ : Float := 2 * C.a₄ + C.a₁ * C.a₃

/-- `WeierstrassCurve.b₆`. -/
def b₆ : Float := C.a₃ * C.a₃ + 4 * C.a₆

/-- `W.Ψ₂Sq.eval x`, the 2-division polynomial $4x^3 + b_2x^2 + 2b_4x + b_6$ in Horner form. -/
def evalΨ₂Sq (x : Float) : Float := ((4 * x + C.b₂) * x + 2 * C.b₄) * x + C.b₆

/-- The derivative $12x^2 + 2b_2x + 2b_4$ of `evalΨ₂Sq`, for the Newton polish in `e₁`. -/
def evalDerivΨ₂Sq (x : Float) : Float := (12 * x + 2 * C.b₂) * x + 2 * C.b₄

/-- `WeierstrassCurve.realPeriodIntegrand`. Over `ℝ` the junk value where the cubic is not
positive comes out of `√v = 0` and `0⁻¹ = 0`; in `Float` the same two conventions would give
`1 / 0 = ∞`, so they are spelled out. -/
def integrand (x : Float) : Float :=
  let v := C.evalΨ₂Sq x
  if v ≤ 0 then 0 else 1 / v.sqrt

/-- `n` steps of Newton's method for `evalΨ₂Sq` from `x`. -/
def newton (C : LMFDBCurve) : Nat → Float → Float
  | 0, x => x
  | n + 1, x =>
    let d := C.evalDerivΨ₂Sq x
    newton C n (if d == 0 then x else x - C.evalΨ₂Sq x / d)

/-- `WeierstrassCurve.e₁`, the largest real root of $4x^3 + b_2x^2 + 2b_4x + b_6$. Depressing the
cubic to $y^3 + Ay + B$ by $x = y - b_2/12$, the largest root is $2\sqrt{-A/3}\cos(\frac13\arccos
c)$ with $c = \frac{3B}{2A}\sqrt{-3/A}$ when $A < 0$ and $|c| \leq 1$, which is the case of three
real roots; the remaining cases are the hyperbolic analogues. The trigonometric form is used in
preference to Cardano's because Cardano's needs cube roots of complex numbers in precisely that
first case, and loses accuracy doing so. Newton removes the rounding error of the closed
form. -/
def e₁ : Float :=
  let p := C.b₂ / 4
  let q := C.b₄ / 2
  let r := C.b₆ / 4
  let A := q - p * p / 3
  let B := 2 * p * p * p / 27 - p * q / 3 + r
  let y :=
    if A < 0 then
      let m := 2 * (-A / 3).sqrt
      let c := 3 * B / (2 * A) * (-3 / A).sqrt
      if c.abs ≤ 1 then m * (c.acos / 3).cos
      else (if B ≤ 0 then m else -m) * (c.abs.acosh / 3).cosh
    else if 0 < A then -2 * (A / 3).sqrt * ((3 * B / (2 * A) * (3 / A).sqrt).asinh / 3).sinh
    else -B.cbrt
  newton C 6 (y - p / 3)

/-! ## Double-exponential quadrature -/

/-- The number of quadrature nodes on each side of $t = 0$. -/
def numNodes : Nat := 1400

/-- The spacing of the quadrature nodes. -/
def nodeStep : Float := 1 / 256

/-- Nodes with $|\frac{\pi}{2}\sinh t|$ beyond this contribute less than the rounding error, and
$\cosh^2$ of it would overflow. -/
def nodeCap : Float := 150

/-- $\sum_k h \, g(t_k, \frac{\pi}{2}\sinh t_k)$ over the nodes $t_k = kh$, $|k| \leq$ `numNodes`,
the shape shared by the two double-exponential rules below. -/
def deSum (g : Float → Float → Float) : Float :=
  nodeStep * (List.range (2 * numNodes + 1)).foldl (init := 0) fun s k =>
    let t := nodeStep * (k.toFloat - numNodes.toFloat)
    let u := pi / 2 * t.sinh
    if nodeCap < u.abs then s else s + g t u

/-- $\int_a^b f$ by the $\tanh$-$\sinh$ rule, $x = \frac{a+b}{2} + \frac{b-a}{2}\tanh(\frac{\pi}{2}
\sinh t)$. The nodes crowd into the endpoints doubly exponentially, which is what makes an
inverse-square-root singularity there harmless. -/
def tanhSinh (f : Float → Float) (a b : Float) : Float :=
  let c := (a + b) / 2
  let d := (b - a) / 2
  deSum fun t u => d * (pi / 2) * t.cosh / (u.cosh * u.cosh) * f (c + d * u.tanh)

/-- $\int_0^\infty f$ by the $\exp$-$\sinh$ rule, $x = \exp(\frac{\pi}{2}\sinh t)$. -/
def expSinh (f : Float → Float) : Float :=
  deSum fun t u => let s := u.exp; s * (pi / 2) * t.cosh * f s

/-! ## The two integrators -/

/-- The coefficients $c, d$ of the quadratic cofactor: $4x^3 + b_2x^2 + 2b_4x + b_6 =
(x - e_1)(4x^2 + cx + d)$, by synthetic division. This is
`WeierstrassCurve.exists_Ψ₂Sq_eq_X_sub_C_mul` made explicit, and $e_2, e_3$ are read off it as
$(-c \pm \sqrt{c^2 - 16d})/8$ rather than from the closed form for the cubic. Deflating is what
makes the factorisation hold to machine precision for the same $e_1$ that the substitutions in
`leastRealPeriodIntegral` and `ovalIntegral` are built on; solving for the three roots
independently would leave those identities only approximately true, and the substitutions would
lose the exact cancellation they rely on. -/
def cofactor : Float × Float :=
  let c := C.b₂ + 4 * C.e₁
  (c, 2 * C.b₄ + c * C.e₁)

/-- `WeierstrassCurve.leastRealPeriodIntegral`, $2\int_{e_1}^\infty \frac{dx}{\sqrt{\Psi_2^2(x)}}$.
Substituting $x = e_1 + s^2$ turns it into $\int_0^\infty \frac{4\,ds}{\sqrt{G(e_1 + s^2)}}$,
where $G = 4X^2 + cX + d$ is the cofactor: the $s$ from $\sqrt{x - e_1}$ cancels against the
Jacobian $2s$, leaving nothing singular. -/
def leastRealPeriodIntegral : Float :=
  let r := C.e₁
  let (c, d) := C.cofactor
  2 * expSinh fun s => 2 / ((4 * (r + s * s) + c) * (r + s * s) + d).sqrt

/-- $\int_{e_3}^{e_2} \frac{dx}{\sqrt{\Psi_2^2(x)}}$ over the bounded oval, and $0$ when
$\Delta < 0$ and there is no oval. Substituting $x = \frac{e_2+e_3}{2} + \frac{e_2-e_3}{2}\sin
\theta$ makes $\sqrt{(x - e_2)(x - e_3)}$ equal to $\frac{e_2-e_3}{2}\cos\theta$, which cancels
against the Jacobian and leaves $\frac{1}{2\sqrt{e_1 - x}}$. -/
def ovalIntegral : Float :=
  let r := C.e₁
  let (c, d) := C.cofactor
  let disc := c * c - 16 * d
  if disc ≤ 0 then 0 else
    let m := -c / 8
    let R := disc.sqrt / 8
    tanhSinh (fun θ => 1 / (2 * (r - (m + R * θ.sin)).sqrt)) (-(pi / 2)) (pi / 2)

/-- `WeierstrassCurve.realPeriodIntegral`, $2\int_{\mathbb{R}}\frac{dx}{\sqrt{\Psi_2^2(x)}}$: the
support of the integrand is the identity component $(e_1, \infty)$ together with the oval
$(e_3, e_2)$, so this is `leastRealPeriodIntegral` plus twice `ovalIntegral`. -/
def realPeriodIntegral : Float := C.leastRealPeriodIntegral + 2 * C.ovalIntegral

/-- The same number computed by handing `integrand` itself to the quadrature — the definition
transcribed literally, with no analytic preparation. Accurate to between $10^{-10}$ and
$10^{-5}$ relative, depending on how much cancellation the coefficients cause; see the module
docstring. -/
def naiveRealPeriodIntegral : Float :=
  let r := C.e₁
  let (c, d) := C.cofactor
  let disc := c * c - 16 * d
  let identity := expSinh fun s => C.integrand (r + s)
  let oval := if disc ≤ 0 then 0 else
    tanhSinh C.integrand ((-c - disc.sqrt) / 8) ((-c + disc.sqrt) / 8)
  2 * (identity + oval)

/-! ## The comparisons -/

/-- How far `realPeriodIntegral` is from the LMFDB's value, relative to it. -/
def relError : Float := (C.realPeriodIntegral - C.realPeriod).abs / C.realPeriod

/-- How far `naiveRealPeriodIntegral` is from the LMFDB's value, relative to it. -/
def naiveRelError : Float := (C.naiveRealPeriodIntegral - C.realPeriod).abs / C.realPeriod

/-- `realPeriodIntegral` agrees with the LMFDB to the precision of a `Float`. -/
def agrees : Bool := C.relError < 1e-14

/-- `naiveRealPeriodIntegral` agrees with the LMFDB as closely as its cancellation error allows. -/
def naiveAgrees : Bool := C.naiveRelError < 1e-4

/-- The sign of $\Delta$ agrees with the number of real roots of $\Psi_2^2$: this is the
hypothesis that `WeierstrassCurve.realPeriodIntegral_of_pos` and
`WeierstrassCurve.realPeriodIntegral_of_neg` are stated in. -/
def discSignAgrees : Bool :=
  let (c, d) := C.cofactor
  (0 < C.disc) == (0 < c * c - 16 * d)

end LMFDBCurve

/-! ## The correspondence with the definitions over `ℝ`

The `Float` transcription is only as good as the formulas it transcribes; these pin the algebraic
ones to the definitions they are supposed to mirror. -/

section Correspondence

variable (W : WeierstrassCurve ℝ) (x : ℝ)

example : W.b₂ = W.a₁ * W.a₁ + 4 * W.a₂ := by rw [WeierstrassCurve.b₂]; ring

example : W.b₄ = 2 * W.a₄ + W.a₁ * W.a₃ := by rw [WeierstrassCurve.b₄]

example : W.b₆ = W.a₃ * W.a₃ + 4 * W.a₆ := by rw [WeierstrassCurve.b₆]; ring

example : W.Ψ₂Sq.eval x = ((4 * x + W.b₂) * x + 2 * W.b₄) * x + W.b₆ := by
  simp [WeierstrassCurve.Ψ₂Sq]; ring

example : W.realPeriodIntegrand x = (√(W.Ψ₂Sq.eval x))⁻¹ := rfl

example : W.realPeriodIntegral = 2 * ∫ x, W.realPeriodIntegrand x := rfl

example : W.leastRealPeriodIntegral = 2 * ∫ x in Set.Ioi W.e₁, W.realPeriodIntegrand x := rfl

end Correspondence

/-! ## The curves -/

/-- Twenty curves from the LMFDB, in the field order
`label, a₁, a₂, a₃, a₄, a₆, rank, torsion, disc, realPeriod`. -/
def lmfdbCurves : List LMFDBCurve := [
  ⟨"11.a1", 0, -1, 1, -7820, -263580, 0, 1, -11, 0.253841860855911⟩,
  ⟨"11.a2", 0, -1, 1, -10, -20, 0, 5, -161051, 1.26920930427955⟩,
  ⟨"11.a3", 0, -1, 1, 0, 0, 0, 5, -11, 6.34604652139777⟩,
  ⟨"14.a1", 1, 0, 1, -2731, -55146, 0, 2, 25088, 0.660447318688961⟩,
  ⟨"14.a3", 1, 0, 1, -36, -70, 0, 6, 941192, 1.98134195606688⟩,
  ⟨"15.a2", 1, 1, 1, -135, -660, 0, 4, 164025, 1.40060304233260⟩,
  ⟨"15.a5", 1, 1, 1, -10, -10, 0, 8, 50625, 2.80120608466520⟩,
  ⟨"19.a2", 0, 1, 1, -9, -15, 0, 3, -6859, 1.35975973348831⟩,
  ⟨"26.b2", 1, -1, 1, -3, 3, 0, 7, -1664, 4.34675744684339⟩,
  ⟨"30.a6", 1, 0, 1, -19, 26, 0, 12, 72900, 3.35194825924150⟩,
  ⟨"37.a1", 0, 0, 1, -1, 0, 1, 1, 37, 5.98691729246392⟩,
  ⟨"43.a1", 0, 1, 1, 0, 0, 1, 1, -43, 5.46868952996758⟩,
  ⟨"53.a1", 1, -1, 1, 0, 0, 1, 1, -53, 4.68764104887888⟩,
  ⟨"54.b2", 1, -1, 1, -14, 29, 0, 9, -124416, 3.09156554910301⟩,
  ⟨"57.a1", 0, -1, 1, -2, 2, 1, 1, -171, 5.55550452137250⟩,
  ⟨"66.c3", 1, 0, 0, -45, 81, 0, 10, 2737152, 2.38322963122497⟩,
  ⟨"210.e6", 1, 0, 0, -1070, 7812, 0, 16, 51438240000, 1.02593301001953⟩,
  ⟨"389.a1", 0, 1, 1, -2, 0, 2, 1, 389, 4.98042512171011⟩,
  ⟨"433.a1", 1, 0, 0, 0, 1, 2, 1, -433, 4.21471019299848⟩,
  ⟨"5077.a1", 0, 0, 1, -7, 6, 3, 1, 5077, 4.15168798308693⟩]

/-! ## The computed values -/

/-- `n` decimal digits of the fractional part of `f`, where `0 ≤ f < 1`. -/
def fracDigits : Nat → Float → String
  | 0, _ => ""
  | n + 1, f =>
    let g := f * 10
    let d := g.floor
    toString d.toUInt64.toNat ++ fracDigits n (g - d)

/-- `x` as a decimal string with `n` digits after the point, rounded, for `0 ≤ x`. -/
def toDecimal (n : Nat) (x : Float) : String :=
  let x := x + 0.5 * (10 : Float) ^ (-n.toFloat)
  toString x.floor.toUInt64.toNat ++ "." ++ fracDigits n (x - x.floor)

/-- One line per curve: the label, `realPeriodIntegral`, the LMFDB's `real_period`, and the
relative difference in units of $10^{-15}$. `#eval IO.println report` prints the table that the
module docstring quotes. -/
def report : String :=
  String.intercalate "\n" <| lmfdbCurves.map fun C =>
    s!"{C.label} {toDecimal 15 C.realPeriodIntegral} {toDecimal 15 C.realPeriod} \
{toDecimal 2 (C.relError * 1e15)}"

/-! ## The checks

As of the data above, the worst relative disagreement with the LMFDB is $3.3 \cdot 10^{-15}$
for `realPeriodIntegral` (`11.a1`) and $2.9 \cdot 10^{-5}$ for `naiveRealPeriodIntegral`
(`14.a1`, whose $a_4 = -2731$ and $a_6 = -55146$ leave the cubic nothing to cancel against). -/

#guard lmfdbCurves.length = 20

-- both signs of the discriminant occur
#guard lmfdbCurves.any (·.disc < 0) && lmfdbCurves.any (0 < ·.disc)

-- ranks `0` to `3` all occur
#guard [0, 1, 2, 3].all fun r => lmfdbCurves.any (·.rank == r)

-- at least four distinct torsion orders occur
#guard 4 ≤ (lmfdbCurves.map (·.torsion)).eraseDups.length

#guard lmfdbCurves.all (·.discSignAgrees)

#guard lmfdbCurves.all (·.agrees)

#guard lmfdbCurves.all (·.naiveAgrees)

end WeierstrassCurve.PeriodIntegralTest
