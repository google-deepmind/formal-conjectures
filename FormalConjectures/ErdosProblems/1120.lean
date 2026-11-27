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
# Erdős Problem 1120

*References:*
- [erdosproblems.com/1120](https://www.erdosproblems.com/1120)
- [Ha74] Hayman, W. K., *Research problems in function theory: new problems*. Proceedings of
  the Symposium on Complex Analysis (Canterbury, 1973), London Math. Soc. Lecture Note Ser. 12
  (1974), 155--180.
-/

@[expose] public section

open Polynomial MeasureTheory ENNReal Filter Topology

namespace Erdos1120

/-- The length of a subset of $\mathbb{C}$: its one-dimensional Hausdorff measure, as in
`Erdos1041`. -/
noncomputable def length (s : Set ℂ) : ℝ≥0∞ := μH[1] s

/-- The shortest length of a path in $E = \{z : \lvert f(z)\rvert \le 1\}$ joining $0$ to the unit
circle. -/
noncomputable def L (f : ℂ[X]) : ℝ≥0∞ :=
  ⨅ (w : ℂ) (_ : ‖w‖ = 1) (γ : Path (0 : ℂ) w) (_ : Set.range γ ⊆ {z | ‖f.eval z‖ ≤ 1}),
    length (Set.range γ)

/-- The worst case of `L f` over monic polynomials of degree $n$ with all roots in
$\lvert z\rvert \le 1$. -/
noncomputable def W (n : ℕ) : ℝ≥0∞ :=
  ⨆ (f : ℂ[X]) (_ : f.Monic ∧ f.natDegree = n ∧ f.rootSet ℂ ⊆ Metric.closedBall 0 1), L f

def erdos_1120.answer : ℕ → ℝ≥0∞ := by sorry

/--
Let $f \in \mathbb{C}[z]$ be monic of degree $n$, with all roots satisfying $\lvert z\rvert \le 1$.
Let $E = \{z : \lvert f(z)\rvert \le 1\}$. What is the shortest length of a path in $E$ joining
$z = 0$ to $\lvert z\rvert = 1$?

This is Problem 4.22 of [Ha74], where it is attributed to Erdős. We formalize the worst case over
all such $f$ of degree $n$, which is the quantity of interest on the problem page.
-/
@[category research open, question value, AMS 30]
theorem erdos_1120 (n : ℕ) : W n = erdos_1120.answer n := by
  sorry

/-- Erdős wrote that the worst-case length "presumably tends to infinity with $n$". -/
@[category research open, AMS 30]
theorem erdos_1120.variants.tendsto_top : Tendsto W atTop (𝓝 ⊤) := by
  sorry

/-- Clunie and Netanyahu (personal communication, reported in [Ha74]): $E$ always contains a path
joining $0$ to the unit circle. -/
@[category research solved, AMS 30]
theorem erdos_1120.variants.exists_path (f : ℂ[X]) (hf : f.Monic)
    (hroots : f.rootSet ℂ ⊆ Metric.closedBall 0 1) :
    ∃ w : ℂ, ‖w‖ = 1 ∧ ∃ γ : Path (0 : ℂ) w, Set.range γ ⊆ {z | ‖f.eval z‖ ≤ 1} := by
  sorry

end Erdos1120
