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
# Erdős Problem 908

A conjecture of de Bruijn and Erdős asking whether every function with measurable
differences can be decomposed as the sum of a continuous function, an additive function,
and a function that is almost periodic for every period. Answered affirmatively by
Laczkovich.

*Reference:* [erdosproblems.com/908](https://www.erdosproblems.com/908)

[La80] Laczkovich, M., _Functions with measurable differences_, 1980.
-/

open MeasureTheory

namespace Erdos908

/--
Erdős Problem 908 (proved by Laczkovich [La80]):

Let $f : \mathbb{R} \to \mathbb{R}$ be such that for every $h > 0$, the function
$x \mapsto f(x + h) - f(x)$ is measurable. Is it true that $f = g + \varphi + r$ where
$g$ is continuous, $\varphi$ is additive (i.e., $\varphi(x + y) = \varphi(x) + \varphi(y)$),
and $r(x + h) - r(x) = 0$ for every $h$ and almost all (depending on $h$) $x$?

A conjecture of de Bruijn and Erdős. Answered in the affirmative by Laczkovich.
See also [907].
-/
@[category research solved, AMS 26 28]
theorem erdos_908 : answer(True) ↔
    ∀ f : ℝ → ℝ, (∀ h : ℝ, h > 0 → Measurable (fun x => f (x + h) - f x)) →
    ∃ g φ r : ℝ → ℝ, Continuous g ∧ (∀ x y : ℝ, φ (x + y) = φ x + φ y) ∧
      (∀ h : ℝ, h > 0 → ∀ᵐ x ∂volume, r (x + h) - r x = 0) ∧
      ∀ x : ℝ, f x = g x + φ x + r x := by
  sorry

end Erdos908
