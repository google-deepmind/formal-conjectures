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
# Erdős Problem 989

*References:*
- [erdosproblems.com/989](https://www.erdosproblems.com/989)
- [Be87] Beck, József, *Irregularities of distribution. I*. Acta Math. (1987), 1--49.
- [Er64b] Erdős, P., *Problems and results on diophantine approximations*. Compositio Math. (1964),
  52-65.
-/

open Filter
open scoped EuclideanGeometry Real

namespace Erdos989

/-- A point set in the plane is discrete if it meets every closed disk in a finite set. -/
def IsDiscretePointSet (A : Set ℝ²) : Prop :=
  ∀ (x : ℝ²) (r : ℝ), (A ∩ Metric.closedBall x r).Finite

/--
The absolute discrepancy between the number of points of `A` in the closed disk of radius `r`
centred at `x` and the area $\pi r^2$ of that disk.

The problem writes "circles"; the comparison with area identifies these as disks.
-/
noncomputable def diskDiscrepancy (A : Set ℝ²) (x : ℝ²) (r : ℝ) : ℝ :=
  |((A ∩ Metric.closedBall x r).ncard : ℝ) - π * r ^ 2|

/-- Finite point sets are discrete. -/
@[category API, AMS 52]
theorem isDiscretePointSet_of_finite {A : Set ℝ²} (hA : A.Finite) : IsDiscretePointSet A :=
  fun _ _ => hA.inter_of_left _

/-- The empty set has discrepancy equal to the area of the disk. -/
@[category test, AMS 52]
theorem diskDiscrepancy_empty (x : ℝ²) (r : ℝ) :
    diskDiscrepancy (∅ : Set ℝ²) x r = |π * r ^ 2| := by
  simp [diskDiscrepancy]

/--
If $A=\{z_1,z_2,\ldots \}\in \mathbb{R}^2$ is an infinite sequence then let
$$f(r)=\max_C \left\lvert \lvert A\cap C\rvert-\pi r^2\right\rvert,$$
where the maximum is taken over all circles $C$ of radius $r$.

Is $f(r)$ unbounded for every $A$? How fast does $f(r)$ grow?

This was settled by Beck [Be87], who proved that
$$f(r) \gg r^{1/2}$$
for all $A$, and there exists $A$ such that
$$f(r) \ll (r\log r)^{1/2}.$$

The set $A$ is taken to be discrete (locally finite), so that $A\cap C$ is finite for every disk $C$.
-/
@[category research solved, AMS 52]
theorem erdos_989.parts.i :
    answer(True) ↔
      ∀ (A : Set ℝ²), A.Infinite → IsDiscretePointSet A →
        ∀ M : ℝ, ∃ r > 0, ∃ x : ℝ², M < diskDiscrepancy A x r := by
  sorry

/--
This was settled by Beck [Be87], who proved that
$$f(r) \gg r^{1/2}$$
for all $A$.
-/
@[category research solved, AMS 52]
theorem erdos_989.variants.beck_lower :
    ∃ C > (0 : ℝ), ∀ (A : Set ℝ²), A.Infinite → IsDiscretePointSet A →
      ∀ᶠ r : ℝ in atTop, ∃ x : ℝ², C * Real.sqrt r ≤ diskDiscrepancy A x r := by
  sorry

/--
This was settled by Beck [Be87], who proved that there exists $A$ such that
$$f(r) \ll (r\log r)^{1/2}.$$
-/
@[category research solved, AMS 52]
theorem erdos_989.variants.beck_upper :
    ∃ (A : Set ℝ²), A.Infinite ∧ IsDiscretePointSet A ∧
      ∃ C > (0 : ℝ), ∀ᶠ r : ℝ in atTop,
        ∀ x : ℝ², diskDiscrepancy A x r ≤ C * Real.sqrt (r * Real.log r) := by
  sorry

end Erdos989
