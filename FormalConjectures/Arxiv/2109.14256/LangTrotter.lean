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

*Reference:* [arxiv/2109.14256](https://arxiv.org/abs/2109.14256)
**Lang–Trotter Conjecture for CM Elliptic Curves**
by *Daqing Wan* and *Ping Xi*, Conjecture 1.2.

The original conjecture is due to S. Lang and H. Trotter, *Frobenius distributions in
`GL₂`-extensions*, Lecture Notes in Mathematics 504, Springer, 1976.
-/

namespace Arxiv.«2109.14256»

open Filter Topology WeierstrassCurve

/-- The trace of Frobenius `a_p(E)` at a prime `p` of an elliptic curve `E` over `ℚ`.

It is defined by `|E(𝔽_p)| = p + 1 - a_p(E)`, where `E(𝔽_p)` is the group of points of the
reduction at `p` of a minimal Weierstrass model of `E` over `ℤ_[p]`. This is the same recipe
that `WeierstrassCurve.localPolynomial` uses. The value is only meaningful at primes of good
reduction. -/
noncomputable def trace (E : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime] : ℤ :=
  (p : ℤ) + 1 - Nat.card
    (((E.baseChange ℚ_[p]).minimal ℤ_[p]).reduction ℤ_[p]).toAffine.Point

/-- A prime `p` is *good* for `E` if `E` has good reduction at `p`, i.e. if `p ∤ N_E`. -/
def GoodPrime (E : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime] : Prop :=
  ((E.baseChange ℚ_[p]).minimal ℤ_[p]).HasGoodReduction ℤ_[p]

/-- The Lang–Trotter counting function
`π_{E,r}(x) = |{p ≤ x : a_p(E) = r, p ∤ N_E}|`. -/
noncomputable def primeCount (E : WeierstrassCurve ℚ) (r : ℤ) (x : ℝ) : ℕ :=
  Nat.card {p : Nat.Primes | letI := Fact.mk p.2
    (p : ℝ) ≤ x ∧ GoodPrime E p ∧ trace E p = r}

/-- An elliptic curve over `ℚ` has *complex multiplication* if and only if its `j`-invariant is
one of the thirteen `j`-invariants of CM elliptic curves over `ℚ`, corresponding to the
imaginary quadratic orders of class number one. -/
def HasCM (E : WeierstrassCurve ℚ) [E.IsElliptic] : Prop :=
  E.j ∈ ({0, 1728, -3375, 8000, 54000, 287496, -32768, -884736, 16581375, -12288000,
    -884736000, -147197952000, -262537412640768000} : Set ℚ)

/-- **The Lang–Trotter conjecture.** Let `E` be an elliptic curve over `ℚ` and let `r` be an
integer, with `r ≠ 0` if `E` has complex multiplication. Then
$$\pi_{E,r}(x) \sim c_{E,r}\frac{\sqrt{x}}{\log x}$$
for a constant `c_{E,r} ≥ 0` that can be described in terms of the image of the associated
Galois representation.

If `c_{E,r} = 0`, the asymptotic formula is interpreted as saying that there are only finitely
many primes `p` with `a_p(E) = r`; the limit formulation below covers both cases. The case
`r = 0` of a CM curve is excluded because then `π_{E,0}(x) ∼ x / (2 \log x)`, by a classical
result of Deuring.

The constant `c_{E,r}` is left existentially quantified here because no closed form for it is
available in general; see the note below on its conjectural description. -/
@[category research open, AMS 11 14]
theorem lang_trotter (E : WeierstrassCurve ℚ) [E.IsElliptic] (r : ℤ)
    (hr : HasCM E → r ≠ 0) :
    ∃ c : ℝ, 0 ≤ c ∧
      Tendsto (fun x : ℝ ↦ primeCount E r x * Real.log x / Real.sqrt x) atTop (𝓝 c) := by
  sorry

/-
### The Lang–Trotter constant

The constant `c_{E,r}` is not given by an explicit formula: it is described in terms of the
image of the Galois representation on the torsion of `E`, and the source stresses that even
this description is conjectural and hard to evaluate for a given pair `(E, r)`.

For a subgroup `G ≤ GL₂(ℤ/nℤ)` write `G_r := {g ∈ G : tr g ≡ r (mod n)}`. Let `E` have CM by
the imaginary quadratic field `K = ℚ(√(-D))` with `D ≥ 1` squarefree, and let `R_D` be the
relevant order, so that the Galois action on torsion gives
`ρ_E : Gal(ℚ̄/K) → GL₁(R_D)`, whose image has finite index by Serre. Let `m_E` be the least
`m₀ ≥ 1` such that `Gal(K(E[m])/K) = π⁻¹(Gal(K(E[gcd (m, m₀)])/K))` for every `m ≥ 1`, where
`π` is the projection `(R_D/mR_D)ˣ → (R_D/gcd (m, m₀)R_D)ˣ`, taken divisible by `4p` for every
prime `p` ramified in `R_D`. Viewing `GL₁(R_D/mR_D)` inside `GL₂(ℤ/mℤ)` via a `ℤ/mℤ`-basis of
`R_D/mR_D`, N. Jones interpreted the constant as
$$
  c_{E,r} = \frac{m_E}{2} \cdot
    \frac{|\mathrm{Gal}(K(E[m_E])/K)_r|}{|\mathrm{Gal}(K(E[m_E])/K)|} \cdot
    \prod_{p \mid r,\; p \nmid m_E} \left(1 - \frac{\left(\frac{-D}{p}\right)}{p}\right)^{-1}
    \prod_{p \nmid r m_E}
      \left(1 - \frac{\left(\frac{-D}{p}\right)}{(p - 1)\left(p - \left(\frac{-D}{p}\right)\right)}
      \right),
$$
where `(-D/p)` is the Legendre symbol. See equation (1.3) and Section 7.4 of the source, and
N. Jones, *Averages of elliptic curve constants*, Math. Ann. 345 (2009), Section 2.2.

In particular `c_{E,r} > 0` if and only if the Galois image contains an element of trace `r`,
so `c_{E,r} = 0` exactly when there is a congruence obstruction. For example `c_{E,2} > 0`
always, since the identity matrix has trace `2`.

The main point of the source is to replace this description by an analytically defined constant
`𝔠_{E,r}` that is completely explicit, and to conjecture that `c_{E,r} = 𝔠_{E,r}`
(Conjecture 1.5, the Comparison Conjecture).
-/

end Arxiv.«2109.14256»
