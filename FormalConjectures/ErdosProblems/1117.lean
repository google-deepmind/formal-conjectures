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
# Erdős Problem 1117

*References:*
- [erdosproblems.com/1117](https://www.erdosproblems.com/1117)
- [GlPa24] Glücksam, Adi and Pardo-Simón, Leticia, An approximate solution to Erdős' maximum modulus
  points problem. J. Math. Anal. Appl. (2024), Paper No. 127768, 20.
- [Ha74] Hayman, W. K., Research problems in function theory: new problems. (1974), 155--180.
- [HePi68] Herzog, F. and Piranian, G., The counting function for points of maximum modulus. (1968),
  240--243.
-/

open Filter

namespace Erdos1117

/--
Let $f(z)$ be an entire function which is not a monomial. Let $\nu(r)$ count the number of $z$ with
$\lvert z\rvert=r$ such that $\lvert f(z)\rvert=\max_{\lvert z\rvert=r}\lvert f(z)\rvert$. (This is
a finite quantity if $f$ is not a monomial.)

Is it possible for\[\limsup \nu(r)=\infty?\]

This is Problem 2.16 in [Ha74], where it is attributed to Erdős.
The answer to the first question is yes, as shown by Herzog and Piranian [HePi68].
-/
@[category research solved, AMS 32]
theorem erdos_1117.part.a :
    answer(True) ↔ ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
    (¬ ∃ (c : ℂ) (n : ℕ), ∀ z, f z = c * z ^ n) ∧
    ∀ N : ℕ, ∃ᶠ r : ℝ in atTop,
      {z | ‖z‖ = r ∧ ‖f z‖ = sSup ((norm ∘ f) '' Metric.sphere 0 r)}.ncard ≥ N := by
  sorry

/--
Is it possible for\[\liminf \nu(r)=\infty?\]

The second question is still open, although an 'approximate' affirmative answer is given by
Glücksam and Pardo-Simón [GlPa24].
-/
@[category research open, AMS 32]
theorem erdos_1117.part.b :
    answer(sorry) ↔ ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
    (¬ ∃ (c : ℂ) (n : ℕ), ∀ z, f z = c * z ^ n) ∧
    Tendsto (fun r : ℝ ↦ {z | ‖z‖ = r ∧ ‖f z‖ = sSup ((norm ∘ f) '' Metric.sphere 0 r)}.ncard)
      atTop atTop := by
  sorry

end Erdos1117
