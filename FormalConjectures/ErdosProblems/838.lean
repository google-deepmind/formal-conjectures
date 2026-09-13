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
# Erdős Problem 838

*References:*
- [erdosproblems.com/838](https://www.erdosproblems.com/838)
- [Er78c] Erdős, P., Some more problems on elementary geometry. Austral. Math. Soc. Gaz. (1978),
  52-54.
-/

open Filter EuclideanGeometry
open scoped Topology EuclideanGeometry

namespace Erdos838

/-- The number of subsets of `P` that are in convex position. -/
noncomputable def convexSubsetCount (P : Finset ℝ²) : ℕ :=
  {S : Finset ℝ² | S ⊆ P ∧ ConvexIndep (S : Set ℝ²)}.ncard

/--
`f n` is maximal such that any `n` points in `ℝ²` with no three on a line determine at least
`f n` different convex subsets (subsets in convex position).
-/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {convexSubsetCount P | (P : Finset ℝ²) (_ : P.card = n)
    (_ : NonTrilinear (P : Set ℝ²))}

/--
Let $f(n)$ be maximal such that any $n$ points in $\mathbb{R}^2$, with no three on a line,
determine at least $f(n)$ different convex subsets. Estimate $f(n)$ - in particular, does there
exist a constant $c$ such that
$$
\lim \frac{\log f(n)}{(\log n)^2}=c?
$$
-/
@[category research open, AMS 52]
theorem erdos_838 :
    answer(sorry) ↔
      ∃ c : ℝ, Tendsto (fun n : ℕ ↦ Real.log (f n : ℝ) / (Real.log (n : ℝ)) ^ 2)
        atTop (𝓝 c) := by
  sorry

/--
A question of Erdős and Hammer. Erdős [Er78c] proved that there exist constants $c_1,c_2>0$
such that
$$
n^{c_1\log n}<f(n)< n^{c_2\log n}.
$$
-/
@[category research solved, AMS 52]
theorem erdos_838.variants.bounds :
    ∃ c1 > (0 : ℝ), ∃ c2 > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (c1 * Real.log (n : ℝ)) < (f n : ℝ) ∧
        (f n : ℝ) < (n : ℝ) ^ (c2 * Real.log (n : ℝ)) := by
  sorry

end Erdos838
