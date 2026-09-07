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
import FormalConjectures.Wikipedia.ModularityConjecture

/-!
# Sato-Tate conjecture

The **Sato-Tate conjecture** describes the distribution of the normalised Frobenius traces
`a_p(E) / (2 √p)` of a non-CM elliptic curve `E` over `ℚ`, as `p` ranges over the primes of
good reduction: they equidistribute in `[-1, 1]` with respect to the **Sato-Tate measure**
`(2 / π) √(1 - x²) dx`.

Originally a conjecture of Mikio Sato and John Tate (independently, around 1960), it is now a
theorem: it was proved for non-CM elliptic curves over totally real fields with some
multiplicative reduction by Clozel, Harris and Taylor and by Taylor (2006-2008), and the
remaining case was settled by Barnet-Lamb, Geraghty, Harris and Taylor (2011). In particular it
holds unconditionally for every non-CM elliptic curve over `ℚ`.

We follow `ModularityConjecture.WeierstrassCurve.ap` for the trace of Frobenius, and state
equidistribution via the density, among primes below `N`, of primes for which the normalised
trace lies in a given subinterval of `[-1, 1]`.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Sato%E2%80%93Tate_conjecture)
- L. Clozel, M. Harris, R. Taylor, *Automorphy for some l-adic lifts of automorphic mod l Galois
  representations*, https://doi.org/10.1007/s10240-008-0016-1
- T. Barnet-Lamb, D. Geraghty, M. Harris, R. Taylor, *A family of Calabi-Yau varieties and
  potential automorphy II*, https://doi.org/10.2977/PRIMS/31
-/

namespace SatoTateConjecture

open ModularityConjecture WeierstrassCurve Filter

/-- The thirteen `j`-invariants of elliptic curves over `ℚ` with complex multiplication,
corresponding to the imaginary quadratic orders of class number one
(discriminants `-3, -4, -7, -8, -11, -12, -16, -19, -27, -28, -43, -67, -163`). -/
def cmJInvariants : Finset ℚ :=
  {0, 1728, -3375, 8000, 54000, 287496, -12288000, 16581375, -884736,
    -884736000, -147197952000, -262537412640768000, 1728}

/-- An elliptic curve `E` over `ℚ` has **complex multiplication** if its `j`-invariant is one of
the thirteen CM `j`-invariants. -/
def HasCM (E : WeierstrassCurve ℚ) [E.IsElliptic] : Prop := E.j ∈ cmJInvariants

/-- The normalised trace of Frobenius `a_p(E) / (2 √p)` at a prime `p` of good reduction. This
lies in `[-1, 1]` by the Hasse bound. -/
noncomputable def normalisedAp (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) : ℝ :=
  (E.ap p : ℝ) / (2 * Real.sqrt p)

/-- The cumulative distribution function of the Sato-Tate measure `(2 / π) √(1 - x²) dx` on
`[-1, 1]`, namely `F(t) = (1 / π) (t √(1 - t²) + arcsin t) + 1 / 2`. -/
noncomputable def satoTateCDF (t : ℝ) : ℝ :=
  (t * Real.sqrt (1 - t ^ 2) + Real.arcsin t) / Real.pi + 1 / 2

/-- The measure that the Sato-Tate distribution assigns to a subinterval `[a, b]` of `[-1, 1]`. -/
noncomputable def satoTateMeasure (a b : ℝ) : ℝ := satoTateCDF b - satoTateCDF a

/-- **The Sato-Tate conjecture** (now a theorem): for a non-CM elliptic curve `E` over `ℚ` and any
`-1 ≤ a ≤ b ≤ 1`, the proportion of primes `p ≤ N` of good reduction for `E` with normalised
trace `a_p(E) / (2 √p) ∈ [a, b]` tends, as `N → ∞`, to the Sato-Tate measure of `[a, b]`.

Proved for elliptic curves over totally real fields (in particular over `ℚ`) by
Clozel-Harris-Taylor, Taylor and Barnet-Lamb-Geraghty-Harris-Taylor. -/
@[category research solved, AMS 11 14]
theorem satoTate_conjecture (E : WeierstrassCurve ℚ) [E.IsElliptic] (hCM : ¬ E.HasCM)
    (a b : ℝ) (ha : -1 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    atTop.Tendsto
      (fun N ↦ ((N.primesBelow.filter
          (fun p ↦ (E.j.den : ZMod p) ≠ 0 ∧ a ≤ E.normalisedAp p ∧ E.normalisedAp p ≤ b)).card /
        (N.primesBelow.card : ℝ)))
      (𝓝 (satoTateMeasure a b)) := by
  sorry

end SatoTateConjecture
