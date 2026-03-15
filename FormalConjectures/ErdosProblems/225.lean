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
# Erdős Problem 225

*Reference:* [erdosproblems.com/225](https://www.erdosproblems.com/225)

Let $f(\theta) = \sum_{k=0}^{n} c_k e^{ik\theta}$ be a trigonometric polynomial all of whose
roots are real (equivalently, the polynomial $P(z) = \sum c_k z^k$ has all roots on
the unit circle), with $\max_{\theta \in [0,2\pi]} |f(\theta)| = 1$. Then
$\int_0^{2\pi} |f(\theta)| \, d\theta \leq 4$.

This was proved independently by Kristiansen [Kr74] (for real $c_k$) and
Saff and Sheil-Small [SaSh74] (for complex $c_k$). The original proof of
Kristiansen contained an error which was later fixed in [Kr76].

[Er40b, Er57, Er61] Erdős, P., original references.

[Ha74] Hayman, W. K., _Research problems in function theory: new problems_ (1974), pp. 155–180,
Problem 4.20.

[Kr74] Kristiansen, G. K., _Proof of an inequality for trigonometric polynomials_.
Proceedings of the American Mathematical Society (1974), pp. 49–57.

[Kr76] Kristiansen, G. K., _Erratum to 'Proof of a polynomial conjecture'_.
Proceedings of the American Mathematical Society (1976), p. 377.

[SaSh74] Saff, E. B. and Sheil-Small, T., _Coefficient and integral mean estimates for algebraic
and trigonometric polynomials with restricted zeros_. Journal of the London Mathematical
Society (2) (1974/75), pp. 16–22.
-/

open Finset BigOperators MeasureTheory

namespace Erdos225

/-- A trigonometric polynomial: $f(\theta) = \sum_{k=0}^{n} c_k e^{ik\theta}$. -/
noncomputable def trigPoly (n : ℕ) (c : ℕ → ℂ) (θ : ℝ) : ℂ :=
  ∑ k ∈ range (n + 1), c k * Complex.exp (↑k * ↑θ * Complex.I)

/--
Erdős Problem 225 [Er40b, Er57, Er61, Ha74]:

If $f(\theta) = \sum_{k=0}^{n} c_k e^{ik\theta}$ is a trigonometric polynomial whose
associated algebraic polynomial $P(z) = \sum c_k z^k$ has all roots on the
unit circle, and $\max_\theta |f(\theta)| = 1$, then
$\int_0^{2\pi} |f(\theta)| \, d\theta \leq 4$.
-/
@[category research solved, AMS 42]
theorem erdos_225 (n : ℕ) (c : ℕ → ℂ)
    (hn : 0 < n)
    (hlead : c n ≠ 0)
    (hroots : ∀ z : ℂ, (∑ k ∈ range (n + 1), c k * z ^ k) = 0 → ‖z‖ = 1)
    (hbound : ∀ θ : ℝ, ‖trigPoly n c θ‖ ≤ 1)
    (hattained : ∃ θ : ℝ, ‖trigPoly n c θ‖ = 1) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖trigPoly n c θ‖ ≤ 4 := by
  sorry

end Erdos225
