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
# Erdős Problem 1147

*References:*
- [erdosproblems.com/1147](https://www.erdosproblems.com/1147)
- [Ko16b] Konieczny, Jakub, *Sets of recurrence as bases for the positive integers*.
  Acta Arith. (2016), 309-338.
-/

open Filter MeasureTheory
open scoped Topology

namespace Erdos1147

/-- Distance to the nearest integer. Written $\|\cdot\|$ in the source. -/
noncomputable abbrev distToInt : ℝ → ℝ := distToNearestInt

/--
The set $A = \{ n \geq 1 : \| \alpha n^2 \| < \varepsilon(n) \}$, where $\|\cdot\|$ denotes
the distance to the nearest integer.
-/
noncomputable def A (α : ℝ) (ε : ℕ → ℝ) : Set ℕ :=
  {n | 1 ≤ n ∧ distToInt (α * n ^ 2) < ε n}

/--
Let $\alpha>0$ be an irrational number. Is the set
$$A=\left\{ n\geq 1: \| \alpha n^2\| < \frac{1}{\log n}\right\},$$
where $\|\cdot\|$ denotes the distance to the nearest integer, an additive basis of order $2$?

Konieczny [Ko16b] disproved this: the claim is false for almost every $\alpha>0$, and also
specifically for $\alpha=\sqrt{2}$.

An additive basis of order $2$ is formalized as an asymptotic additive basis of order $2$: all
sufficiently large natural numbers lie in $A+A$. The exact notion `Set.IsAddBasisOfOrder` would
require $0\in A$, which fails for this $A$.
-/
@[category research solved, AMS 11]
theorem erdos_1147 :
    answer(False) ↔
      ∀ (α : ℝ), 0 < α → Irrational α →
        (A α fun n ↦ 1 / Real.log n).IsAsymptoticAddBasisOfOrder 2 := by
  sorry

/--
The claim is false for almost every $\alpha>0$.
-/
@[category research solved, AMS 11]
theorem erdos_1147.variants.almost_every :
    ∀ᵐ α ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ¬ (A α fun n ↦ 1 / Real.log n).IsAsymptoticAddBasisOfOrder 2 := by
  sorry

/--
The claim is false specifically for $\alpha=\sqrt{2}$.
-/
@[category research solved, AMS 11]
theorem erdos_1147.variants.sqrt_two :
    ¬ (A (Real.sqrt 2) fun n ↦ 1 / Real.log n).IsAsymptoticAddBasisOfOrder 2 := by
  sorry

/--
More generally, given any $\varepsilon(n)\to 0$, the set
$$A=\left\{ n\geq 1: \| \alpha n^2\| < \varepsilon(n)\right\}$$
is not an additive basis of order $2$ for almost every $\alpha>0$.
-/
@[category research solved, AMS 11]
theorem erdos_1147.variants.epsilon (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    ∀ᵐ α ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ¬ (A α ε).IsAsymptoticAddBasisOfOrder 2 := by
  sorry

end Erdos1147
