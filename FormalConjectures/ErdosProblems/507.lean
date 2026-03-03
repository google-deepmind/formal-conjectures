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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 507

*References:*
- [erdosproblems.com/507](https://www.erdosproblems.com/507)
- [CPZ23] Cohen, Alex, Cosmin Pohoata, and Dmitrii Zakharov. "A new upper bound for the Heilbronn
  triangle problem." arXiv preprint arXiv:2305.18253 (2023).
- [CPZ24] Cohen, Alex, Cosmin Pohoata, and Dmitrii Zakharov. "Lower bounds for incidences."
  Inventiones mathematicae (2025): 1-74.
- [KPS82] Komlós, János, János Pintz, and Endre Szemerédi. "A lower bound for Heilbronn's problem."
  Journal of the London Mathematical Society 2.1 (1982): 13-24.
- [KPS81] Komlós, János, János Pintz, and Endre Szemerédi. "On Heilbronn's triangle problem."
  Journal of the London Mathematical Society 2.3 (1981): 385-396.
-/

open Asymptotics Filter Topology
open scoped EuclideanGeometry

namespace Erdos507

/--
The minimum area of a triangle determined by three distinct points in a set `S`.
-/
noncomputable def minTriangleArea (S : Finset ℝ²) : ℝ :=
  sInf {EuclideanGeometry.triangle_area (t.points 0) (t.points 1) (t.points 2) |
    (t : Affine.Triangle ℝ ℝ²) (_ : ∀ i, t.points i ∈ S)}

/--
$\alpha(n)$ is the supremum of `minTriangleArea S` over all sets `S` of $n$ points in the unit disk.
-/
noncomputable def α (n : ℕ) : ℝ :=
  sSup (minTriangleArea '' { S : Finset ℝ² |
    S.card = n ∧ ↑S ⊆ Metric.closedBall (0 : ℝ²) 1 ∧ ¬ Collinear ℝ (S : Set ℝ²) })

/--
Current best lower bound [KPS82].
-/
noncomputable def lowerBest (n : ℕ) : ℝ := Real.log n / (n : ℝ) ^ 2

/--
The "Barrier" function: n^(-7/6) used for the best upper bound [CPZ24].
-/
noncomputable def upperBarrier (n : ℕ) : ℝ := 1 / (n : ℝ) ^ ((7 : ℝ) / 6)

/--
Let $\alpha(n)$ be such that every set of $n$ points in the unit disk contains three points which
determine a triangle of area at most $\alpha(n)$. Estimate $\alpha(n)$.
-/
@[category research open, AMS 51]
theorem erdos_507.equivalent:
    α ~[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/--
Estimate a lower bound for$\alpha(n)$.
-/
@[category research open, AMS 51]
theorem erdos_507.lower:
    let ans := (answer(sorry) : ℕ → ℝ)
    (lowerBest =o[atTop] ans) ∧ (ans ≪ α) := by
  sorry

/--
Estimate an upper bound for$\alpha(n)$.
-/
@[category research open, AMS 51]
theorem erdos_507.upper:
    let ans := (answer(sorry) : ℕ → ℝ)
    (α ≪ ans) ∧ (ans =o[atTop] upperBarrier) := by
  sorry

/--
It is trivial that $\alpha(n) \ll 1/n$.
-/
@[category research formally solved using formal_conjectures at "https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/507.lean", AMS 51]
theorem erdos_507.variants.upper_trivial : α ≪ (fun n ↦ 1 / (n : ℝ)) := by
  sorry

/--
Erdős observed that $\alpha(n) \gg 1/n^2$.
-/
@[category research formally solved using formal_conjectures at "https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/507.lean", AMS 51]
theorem erdos_507.variants.lower_erdos : α ≫ (fun n ↦ 1 / (n : ℝ) ^ 2) := by
  sorry

/--
Current best lower bound [KPS82].
-/
@[category research formally solved using formal_conjectures at "https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/507.lean", AMS 51]
theorem erdos_507.variants.lower_kps82 : lowerBest ≪ α := by
  sorry

/--
Current best upper bound [CPZ24]: $\alpha(n) \ll n^{-7/6 + o(1)}$.
-/
@[category research formally solved using formal_conjectures at "https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/507.lean", AMS 51]
theorem erdos_507.variants.upper_cpz24 :
    ∃ (o : ℕ → ℝ), Tendsto o atTop (𝓝 0) ∧
    α ≪ (fun n ↦ upperBarrier n * (n : ℝ) ^ o n) := by
  sorry

end Erdos507
