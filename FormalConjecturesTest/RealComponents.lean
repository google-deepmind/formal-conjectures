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

import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Data.Real.Basic

/-!
# The number of real components of an elliptic curve

For an elliptic curve $E$ over $\mathbb{R}$ with discriminant $\Delta$, the real locus
$E(\mathbb{R})$ has two connected components if $\Delta > 0$ (three real $2$-torsion points: a
bounded oval and the unbounded component through the point at infinity), and one if $\Delta < 0$
(a single real $2$-torsion point). This file records that count,
`WeierstrassCurve.nrRealComponents`, by the discriminant criterion; the topological
statement is not proved here.

The real period of $E$ in the Birch and Swinnerton-Dyer conjecture is the least positive real
period multiplied by this number: `WeierstrassCurve.realPeriod` (from the period lattice, in
`FormalConjecturesTest.RealPeriod`) and `WeierstrassCurve.realPeriodIntegral` (from the integral
of the invariant differential, in `FormalConjecturesTest.PeriodIntegral`).

*References:*
- [LMFDB](https://beta.lmfdb.org/knowledge/show/ec.q.period_lattice), knowls `ec.q.period_lattice`
  and `ec.q.real_period`
- [Sil1994] Joseph H. Silverman. Advanced Topics in the Arithmetic of Elliptic Curves,
  Chapter V §2, https://link.springer.com/book/10.1007/978-1-4612-0851-8
-/

noncomputable section

namespace WeierstrassCurve

variable (W : WeierstrassCurve ℝ)

/-- The number of connected components of $E(\mathbb{R})$: $2$ if $\Delta > 0$ and $1$ if
$\Delta < 0$, taken as the definition. A singular curve ($\Delta = 0$) is assigned the value $1$. -/
def nrRealComponents : ℕ := if 0 < W.Δ then 2 else 1

lemma nrRealComponents_of_pos (h : 0 < W.Δ) : W.nrRealComponents = 2 := if_pos h

lemma nrRealComponents_of_neg (h : W.Δ < 0) : W.nrRealComponents = 1 := if_neg h.not_gt

lemma nrRealComponents_pos : 0 < W.nrRealComponents := by grind [nrRealComponents]

end WeierstrassCurve

end
