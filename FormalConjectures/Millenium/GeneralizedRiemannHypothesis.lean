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
# Generalized Riemann Hypothesis

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Generalized_Riemann_hypothesis)
-/

namespace GRH

/-- Let $\chi$ be a Dirichlet character, `trivialZeros` is the set of trivial zeros of the
Dirichlet $L$-function of $\chi$ which is always a set of non-positive integers.
- $\chi = 1$ then the Dirichlet $L$-function is the Riemann zeta function, having trivial
  zeroes at all negative even integers (exclude $0$).
- $\chi$ is odd, then the trivial zeroes are the negative odd integers.
- $\chi \neq 1$ is even, then the trivial zeroes are the non-positive even integers. -/
def trivialZeros {q : ℕ} (χ : DirichletCharacter ℂ q) : Set ℤ :=
  if q = 1 then {-2 * (n + 1) | (n : ℕ) } else
    if χ.Odd then { -2 * n - 1 | (n : ℕ) } else
      { - 2 * n | (n : ℕ) }

/-- The **Generalized Riemann Hypothesis** asserts that all the non-trivial zeros of the
Dirichlet $L$-function $L(\chi, s)$ of a primitive Dirichlet character $\chi$ have real part
$\frac{1}{2}$. -/
@[category research open, AMS 11]
theorem generalized_riemann_hypothesis (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (s : ℂ) (hs : χ.LFunction s = 0)
    (hs_nontrivial : s ∉ Int.cast '' trivialZeros χ) :
    s.re = 1 / 2 := by
  sorry

/-- GRH for $\chi = 1$ is `RiemannHypothesis`. -/
@[category test, AMS 11]
theorem implies_riemannHypothesis :
    type_of% (generalized_riemann_hypothesis 1 1) ↔ RiemannHypothesis := by
  aesop (add simp [DirichletCharacter.isPrimitive_one_level_one, trivialZeros,
    RiemannHypothesis, riemannZeta_one_ne_zero])

end GRH
