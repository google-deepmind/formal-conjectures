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
# Dirichlet polynomial avoidance conjecture

*Reference:* S. Shai, *Prime spectroscopy of Riemann zeros* (2026),
https://github.com/SaarShai/Primes-Equispaced .
AI disclosure: conjecture formulated with assistance from Claude (Anthropic).

For a fixed integer `K ≥ 2`, the truncated Möbius Dirichlet polynomial
`c_K(s) = ∑_{k=2}^{K} μ(k) · k^{-s}` is conjectured to be nonzero at every
nontrivial zero of the Riemann zeta function. The polynomial `c_K` itself has
infinitely many zeros in the critical strip (Langer, 1931), so the content of
the conjecture is that none of these coincide with a zeta zero. Numerically,
`c_K(ρ) ≠ 0` has been checked (interval arithmetic) for `K ∈ {10, 20, 50}` at
the first `100` nontrivial zeros `ρ`. The problem is open.
-/

open scoped BigOperators

namespace DirichletPolynomialAvoidance

/-- For every fixed `K ≥ 2` and every nontrivial zero `ρ` of the Riemann
zeta function (`riemannZeta ρ = 0` with `0 < ρ.re < 1`), the truncated
Möbius Dirichlet polynomial `∑_{k=2}^{K} μ(k) · k^{-ρ}` is nonzero. -/
@[category research open, AMS 11]
theorem dirichlet_polynomial_avoidance
    (K : ℕ) (hK : 2 ≤ K)
    (ρ : ℂ) (hρ : riemannZeta ρ = 0)
    (hρ_nontrivial : 0 < ρ.re ∧ ρ.re < 1) :
    (∑ k ∈ Finset.range (K - 1),
      (ArithmeticFunction.moebius (k + 2) : ℂ) * ((k + 2 : ℂ) ^ (-ρ))) ≠ 0 := by
  sorry

end DirichletPolynomialAvoidance
