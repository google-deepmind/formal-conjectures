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
# Erdős Problem 1083

*Reference:* [erdosproblems.com/1083](https://www.erdosproblems.com/1083)
-/

open Filter

namespace Erdos1083

/--
The minimum number of distinct distances determined by an $n$-point subset of
$d$-dimensional Euclidean space.
-/
noncomputable def f (d n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ points : Finset (EuclideanSpace ℝ (Fin d)),
    points.card = n ∧ distinctDistances points = m}

/--
Let $d\geq 3$, and let $f_d(n)$ be the minimal $m$ such that every set of $n$ points in $\mathbb{R}^d$ determines at least $m$ distinct distances. Estimate $f_d(n)$ - in particular, is it true that $$f_d(n)=n^{\frac{2}{d}-o(1)}?$$
-/
@[category research open, AMS 52]
theorem erdos_1083 :
    (∀ d : ℕ, 3 ≤ d → ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ᶠ n : ℕ in atTop,
        (f d n : ℝ) = (n : ℝ) ^ ((2 : ℝ) / (d : ℝ) - o n)) ↔ answer(sorry) := by
  sorry

end Erdos1083
