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
module

public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

/-!
# Real roots of polynomials of odd degree

* `Polynomial.tendsto_atBot_atBot_of_odd_natDegree`: a polynomial of odd degree with nonnegative
  leading coefficient tends to $-\infty$ at $-\infty$.
* `Polynomial.exists_isRoot_of_odd_natDegree`: a real polynomial of odd degree has a real root, by
  the intermediate value theorem.
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
