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

import FormalConjectures.Util.ProblemImports

/-!
# Lonely runner conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Lonely_runner_conjecture)
-/

namespace LonelyRunnerConjecture

/--
Consider $n$ runners on a circular track of unit length. At the initial time
$t = 0$, all runners are at the same position and start to run; the runners'
speeds are constant, all distinct, and may be negative. A runner is said to be
lonely at time $t$ if they are at a distance (measured along the circle) of at
least $\frac 1 n$ from every other runner. The lonely runner conjecture states that each
runner is lonely at some time, no matter the choice of speeds.
-/
@[category research open, AMS 11]
theorem lonely_runner_conjecture (n : ℕ)
    (speed : Fin n ↪ ℝ) (lonely : Fin n → ℝ → Prop)
    (lonely_def :
      ∀ r t, lonely r t ↔
        ∀ r2 : Fin n, r2 ≠ r →
        dist (t * speed r : UnitAddCircle) (t * speed r2) ≥ 1 / n)
    (r : Fin n) : ∃ t ≥ 0, lonely r t := by
  sorry

/-!
## Variant: Tao (2017)
-/

/--
The unit circle $\mathbb{R}/\mathbb{Z}$ seen as `AddCircle (1 : ℝ)`.
-/
abbrev RModZ : Type := AddCircle (1 : ℝ)

/--
Distance in $\mathbb{R}/\mathbb{Z}$ to the nearest integer.
-/
noncomputable def distToInt (t : RModZ) : ℝ :=
  dist t 0

/--
For an $n$-tuple of distinct integer velocities $v_1,\dots,v_n$,
`deltaTuple v` is the maximal value of $\min_i \|t v_i\|_{\mathbb{R}/\mathbb{Z}}$ over time.
-/
noncomputable def deltaTuple {n : ℕ} (v : Fin n ↪ ℤ) : ℝ :=
  sSup { δ : ℝ | ∃ t : RModZ, ∀ i : Fin n, δ ≤ distToInt ((v i) • t) }

/--
The $n$th *gap of loneliness* $\delta_n$: the infimum of `deltaTuple`
over all $n$-tuples of distinct nonzero integer velocities.
-/
noncomputable def deltaGap (n : ℕ) : ℝ :=
  sInf { d : ℝ | ∃ v : Fin n ↪ ℤ, (∀ i : Fin n, v i ≠ 0) ∧ d = deltaTuple v }

/--
**Theorem 1.3 (Tao, 2017; arXiv:1701.02048).**
There exists an absolute constant $c > 0$ such that for all sufficiently large $n$,
the gap of loneliness satisfies
$\delta_n \ge \frac{1}{2n} + \frac{c \log n}{n^2 (\log \log n)^2}$.
-/
@[category research solved, AMS 11]
theorem lonely_runner_conjecture.variants.tao_2017 :
    ∃ c : ℝ, 0 < c ∧
      (∀ᶠ n : ℕ in Filter.atTop,
        deltaGap n ≥
          ((1 : ℝ) / (2 * (n : ℝ))
            + c * Real.log (n : ℝ) /
                ((n : ℝ) ^ 2 * (Real.log (Real.log (n : ℝ))) ^ 2))) := by
  sorry

end LonelyRunnerConjecture
