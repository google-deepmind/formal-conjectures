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
# Erdős Problem 908

*Reference:* [erdosproblems.com/908](https://www.erdosproblems.com/908)
-/

open MeasureTheory Real

namespace Erdos908

/--
Let $f:\mathbb{R}\to \mathbb{R}$ be such that $f(x+h)-f(x)$ is measurable for every $h>0$. Is it
true that
$$
f=g+h+r
$$
where $g$ is continuous, $h$ is additive (so $h(x+y)=h(x)+h(y)$), and $r(x+h)-r(x)=0$ for every $h$
and almost all (depending on $h$) $x$?
-/
@[category research open, AMS 26 28]
theorem erdos_908 :
    answer(sorry) ↔
      ∀ f : ℝ → ℝ,
        (∀ h > 0, Measurable fun x ↦ f (x + h) - f x) →
          ∃ g h r : ℝ → ℝ, Continuous g ∧
            (∀ x y, h (x + y) = h x + h y) ∧
            f = g + h + r ∧
            ∀ t > 0, ∀ᵐ x : ℝ, r (x + t) - r x = 0 := by
  sorry

end Erdos908
