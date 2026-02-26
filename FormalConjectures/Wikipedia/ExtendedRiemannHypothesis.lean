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
# Extended Riemann Hypothesis (Dedekind zeta functions)

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Generalized_Riemann_hypothesis)
-/

namespace ExtendedRiemannHypothesis

/-- The (open) critical strip $\{ s \in \mathbb{C} \mid 0 < \Re(s) < 1 \}$. -/
def IsInCriticalStrip (s : ℂ) : Prop :=
  0 < s.re ∧ s.re < 1

/-- A convenient (over-)approximation to the set of *trivial* zeros of a Dedekind zeta function:
the non-positive integers. -/
def trivialZeros : Set ℤ :=
  Set.Iic 0

/--
The **Extended Riemann Hypothesis** (ERH) for Dedekind zeta functions asserts that if
$K$ is a number field and $\zeta_K(s)$ is its Dedekind zeta function, then every zero of
$\zeta_K(s)$ is either a *trivial* zero (at a non-positive integer) or lies on the critical line
$\Re(s) = \tfrac12$.
-/
@[category research open, AMS 11 12 30]
theorem extended_riemann_hypothesis_dedekindZeta (K : Type*) [Field K] [NumberField K] (s : ℂ)
    (hs : NumberField.dedekindZeta K s = 0)
    (hs_nontrivial : s ∉ Int.cast '' trivialZeros)
    (hs_ne_one : s ≠ 1) :
    s.re = 1 / 2 := by
  sorry

end ExtendedRiemannHypothesis
