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
# Erdős Problem 1126

If `f(x+y) = f(x) + f(y)` for almost all `x, y ∈ ℝ`, then there exists an additive function `g`
such that `f = g` almost everywhere.

*Reference:* [erdosproblems.com/1126](https://www.erdosproblems.com/1126)

[dB66] de Bruijn, N.G., _A difference property for Riemann integrable functions and for
some similar classes of functions_. Indag. Math. 28 (1966), 145-151.

[Ju65] Jurkat, W.B., _On Cauchy's functional equation_. Proc. Amer. Math. Soc. 16 (1965),
683-686.
-/

open MeasureTheory

namespace Erdos1126

/--
Erdős Problem #1126 (proved independently by de Bruijn [dB66] and Jurkat [Ju65]):

If $f(x+y) = f(x) + f(y)$ for almost all $x, y \in \mathbb{R}$ then there exists a function $g$
such that $g(x+y) = g(x) + g(y)$ for all $x, y \in \mathbb{R}$ and $f(x) = g(x)$ for almost
all $x$.
-/
@[category research solved, AMS 28 39]
theorem erdos_1126 (f : ℝ → ℝ)
    (hf : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume), f (p.1 + p.2) = f p.1 + f p.2) :
    ∃ g : ℝ → ℝ,
      (∀ x y : ℝ, g (x + y) = g x + g y) ∧
      (∀ᵐ x ∂volume, f x = g x) := by
  sorry

end Erdos1126
