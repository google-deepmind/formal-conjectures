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
