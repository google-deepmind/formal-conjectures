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
# Erdős Problem 907

*Reference:* [erdosproblems.com/907](https://www.erdosproblems.com/907)

If $f : \mathbb{R} \to \mathbb{R}$ is such that for every $h > 0$ the difference function
$x \mapsto f(x+h) - f(x)$ is continuous, must $f$ decompose as $g + \varphi$ where $g$ is
continuous and $\varphi$ is additive?

[dB51] de Bruijn, N. G., _Functions whose differences belong to a given class_,
Nieuw Arch. Wiskunde (2) 23 (1951), 194-218.
-/

namespace Erdos907

/--
Let $f : \mathbb{R} \to \mathbb{R}$ be such that for every $h > 0$, the function
$x \mapsto f(x + h) - f(x)$ is continuous. Is it true that $f = g + \varphi$ for some
continuous $g$ and additive $\varphi$ (i.e., $\varphi(x + y) = \varphi(x) + \varphi(y)$)?

Answered in the affirmative by de Bruijn [dB51].
-/
@[category research solved, AMS 26 39]
theorem erdos_907 : answer(True) ↔ ∀ (f : ℝ → ℝ),
    (∀ h : ℝ, h > 0 → Continuous (fun x => f (x + h) - f x)) →
    ∃ g φ : ℝ → ℝ, Continuous g ∧ (∀ x y : ℝ, φ (x + y) = φ x + φ y) ∧
      ∀ x : ℝ, f x = g x + φ x := by
  sorry

end Erdos907
