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

import Mathlib.Algebra.CubicDiscriminant
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

/-!
# Real roots of real polynomials

Three facts about polynomials feeding the definition of the real period of an elliptic curve over
$\mathbb{R}$ as an integral (`FormalConjecturesTest.PeriodIntegral`).

* `Polynomial.tendsto_atBot_atBot_of_odd_natDegree`: a polynomial of odd degree with nonnegative
  leading coefficient tends to $-\infty$ at $-\infty$.
* `Polynomial.exists_isRoot_of_odd_natDegree`: a real polynomial of odd degree has a real root, by
  the intermediate value theorem. Hence $\mathbb{R}$ is a real closed field: `Real.isRealClosed`.
* `Cubic.rootMultiplicity_le_one_of_discr_ne_zero`: a cubic with nonzero discriminant has only
  simple roots.
-/

open Filter

namespace Polynomial

section OrderedField

variable {𝕜 : Type*} [NormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜]
  {P : 𝕜[X]}

/-- A polynomial of odd degree with nonnegative leading coefficient tends to $-\infty$ at
$-\infty$: the counterpart at $-\infty$ of `Polynomial.tendsto_atTop_of_leadingCoeff_nonneg`. -/
theorem tendsto_atBot_atBot_of_odd_natDegree (hP : Odd P.natDegree) (hnng : 0 ≤ P.leadingCoeff) :
    Tendsto (fun x ↦ eval x P) atBot atBot := by
  simpa [Function.comp_def] using ((P.comp (-X)).tendsto_atBot_of_leadingCoeff_nonpos
    (by simpa using natDegree_pos_iff_degree_pos.1 hP.pos)
    (by simpa [hP.neg_one_pow] using hnng)).comp tendsto_neg_atBot_atTop

end OrderedField

section Real

variable {p : ℝ[X]}

/-- A real polynomial of odd degree has a real root. Unlike the previous lemma this is stated over
$\mathbb{R}$, not over an arbitrary ordered field: it needs the intermediate value theorem, and a
conditionally complete ordered field is already isomorphic to $\mathbb{R}$. -/
theorem exists_isRoot_of_odd_natDegree (hp : Odd p.natDegree) : ∃ x : ℝ, p.IsRoot x := by
  wlog! hlc : 0 ≤ p.leadingCoeff generalizing p
  · simpa using this (p := -p) (by simpa using hp) (by simpa using hlc.le)
  exact p.continuous.surjective (p.tendsto_atTop_of_leadingCoeff_nonneg
    (natDegree_pos_iff_degree_pos.1 hp.pos) hlc) (tendsto_atBot_atBot_of_odd_natDegree hp hlc) 0

end Real

end Polynomial

/-- The real numbers form a real closed field. -/
instance Real.isRealClosed : IsRealClosed ℝ :=
  .of_linearOrderedField Real.isSquare_iff.2 Polynomial.exists_isRoot_of_odd_natDegree

namespace Cubic

variable {K : Type*} [Field K] {P : Cubic K}

/-- A cubic with nonzero discriminant has only simple roots. -/
theorem rootMultiplicity_le_one_of_discr_ne_zero (ha : P.a ≠ 0) (hd : P.discr ≠ 0) (x : K) :
    Polynomial.rootMultiplicity x P.toPoly ≤ 1 := by
  refine Polynomial.rootMultiplicity_le_one_of_separable ?_ x
  rw [← Polynomial.nodup_aroots_iff_of_splits (K := AlgebraicClosure K) (ne_zero_of_a_ne_zero ha)
    (IsAlgClosed.splits _), Polynomial.aroots_def, ← map_roots]
  exact (discr_ne_zero_iff_roots_nodup ha (IsAlgClosed.splits _)).mp hd

end Cubic
