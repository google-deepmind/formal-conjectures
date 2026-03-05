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
# Erdős Problem 515

*Reference:* [erdosproblems.com/515](https://www.erdosproblems.com/515)

Let $f(z)$ be an entire function, not a polynomial. Does there exist a locally
rectifiable path $C$ tending to infinity such that, for every $\lambda > 0$, the integral
$\int_C |f(z)|^{-\lambda} \, |dz|$ is finite?

This was proved in the affirmative. The case when $f$ has finite order was proved
by Zhang [Zh77]. The general case was proved by Lewis, Rossi, and Weitsman
[LRW84], who in fact proved this with $|f|$ replaced by $e^u$ where $u$ is any
subharmonic function.

[Zh77] Zhang, G., _Asymptotic paths of entire functions_, 1977.

[LRW84] Lewis, J., Rossi, J. and Weitsman, A., _On the growth of subharmonic
functions along paths_, Ark. Mat. 22 (1984), 109-114.
-/

open MeasureTheory Filter Set

namespace Erdos515

/--
Erdős Problem 515: For any entire function $f$ that is not a polynomial, there
exists a locally rectifiable path $\gamma$ tending to infinity such that for every
$\lambda > 0$, the line integral $\int_\gamma |f(z)|^{-\lambda} \, |dz|$ is finite.

The path $\gamma : \mathbb{R} \to \mathbb{C}$ is parametrized on $[0, \infty)$, is continuous
with locally bounded variation (i.e., locally rectifiable), and satisfies
$\|\gamma(t)\| \to \infty$ as $t \to \infty$. The integral
$\int_\gamma |f(z)|^{-\lambda} \, |dz|$ is expressed as
$\int_0^\infty \|f(\gamma(t))\|^{-\lambda} \cdot \|\gamma'(t)\| \, dt$.

The case when $f$ has finite order was proved by Zhang [Zh77]. The general case
was proved by Lewis, Rossi, and Weitsman [LRW84].
-/
@[category research solved, AMS 30]
theorem erdos_515 : answer(True) ↔
    ∀ (f : ℂ → ℂ),
      Differentiable ℂ f →
      (¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z) →
      ∃ (γ : ℝ → ℂ),
        Continuous γ ∧
        LocallyBoundedVariationOn γ (Ici 0) ∧
        Tendsto (fun t => ‖γ t‖) atTop atTop ∧
        ∀ l : ℝ, 0 < l →
          IntegrableOn
            (fun t => ‖f (γ t)‖ ^ (-l) * ‖deriv γ t‖)
            (Ici 0)
            volume := by
  sorry

end Erdos515
