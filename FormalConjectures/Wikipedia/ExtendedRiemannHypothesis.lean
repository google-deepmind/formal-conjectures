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
# Extended Riemann Hypothesis (Dedekind zeta functions)

This file records a benchmark statement for the Extended Riemann Hypothesis (ERH) for Dedekind
zeta functions.

*References:*
* [Wiki-ERH] [Wikipedia: Generalized Riemann hypothesis (Extended Riemann hypothesis)](https://en.wikipedia.org/wiki/Generalized_Riemann_hypothesis#Extended_Riemann_hypothesis)
* [Wiki-Ded] [Wikipedia: Dedekind zeta function](https://en.wikipedia.org/wiki/Dedekind_zeta_function)
* [Neuk99] J. Neukirch, *Algebraic Number Theory*, Springer (Grundlehren 322), 1999, Chapter VII, §5.
* [Mar77] D. A. Marcus, *Number Fields*, Springer (GTM 81), 1977, Chapter VII.

Note: in Mathlib, `NumberField.dedekindZeta` is currently defined as the naive Dirichlet series
(`LSeries`), not as a meromorphic continuation. This file follows Mathlib's naming.
-/

namespace ExtendedRiemannHypothesis

/-- The (open) critical strip $\{ s \in \mathbb{C} \mid 0 < \Re(s) < 1 \}$. -/
def IsInCriticalStrip (s : ℂ) : Prop :=
  0 < s.re ∧ s.re < 1

/--
A convenient (over-)approximation to the set of *trivial* zeros of a Dedekind zeta function.

When $K$ is totally real, the only poles in the completed zeta function come from $\Gamma(s/2)$,
so the trivial zeros occur at non-positive even integers; otherwise $\Gamma(s)$ also appears,
giving trivial zeros at all non-positive integers (see e.g. [Neuk99]).

Informally, the trivial zeros come from the poles of the $\Gamma$-factors in the functional
equation for the completed zeta function. In particular, they occur at non-positive integers, with
the exact pattern depending on the signature of $K$.
-/
def trivialZeros (K : Type*) [Field K] [NumberField K] : Set ℤ :=
  if NumberField.InfinitePlace.nrComplexPlaces K = 0 then
    { -2 * n | (n : ℕ) }
  else
    Set.Iic 0

/--
The **Extended Riemann Hypothesis** (ERH) for Dedekind zeta functions asserts that if
$K$ is a number field and $\zeta_K(s)$ is its Dedekind zeta function, then every zero of
$\zeta_K(s)$ is either a *trivial* zero (at a non-positive integer) or lies on the critical line
$\Re(s) = \tfrac12$.

See also [Wiki-ERH] and [Wiki-Ded].

In the formal statement below, `hs_nontrivial` excludes the chosen set of trivial zeros, and
`hs_ne_one` excludes the (simple) pole at $s = 1$.
-/
@[category research open, AMS 11 12 30]
theorem extended_riemann_hypothesis_dedekindZeta (K : Type*) [Field K] [NumberField K] (s : ℂ)
    (hs : NumberField.dedekindZeta K s = 0)
    (hs_nontrivial : s ∉ Int.cast '' trivialZeros K)
    (hs_ne_one : s ≠ 1) :
    s.re = 1 / 2 := by
  sorry

/--
A common formulation of ERH: every zero of $\zeta_K$ in the critical strip lies on the critical
line.
-/
@[category API, AMS 11 12 30]
theorem extended_riemann_hypothesis_dedekindZeta_of_isInCriticalStrip (K : Type*) [Field K]
    [NumberField K] (s : ℂ) (hs_strip : IsInCriticalStrip s)
    (hs : NumberField.dedekindZeta K s = 0) :
    s.re = 1 / 2 := by
  apply extended_riemann_hypothesis_dedekindZeta (K := K) (s := s) (hs := hs)
  · intro hs_trivial
    rcases hs_trivial with ⟨z, hz, rfl⟩
    rcases hs_strip with ⟨hs_re_pos, _⟩
    have hz_le : (z : ℝ) ≤ 0 := by
      have hz_le_int : z ≤ 0 := by
        by_cases h : NumberField.InfinitePlace.nrComplexPlaces K = 0
        · simp [trivialZeros, h] at hz
          rcases hz with ⟨n, rfl⟩
          have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast (Nat.zero_le n)
          exact mul_nonpos_of_nonpos_of_nonneg (by norm_num : (-2 : ℤ) ≤ 0) hn
        · simpa [trivialZeros, h] using hz
      exact_mod_cast hz_le_int
    exact (not_lt_of_ge hz_le) (by simpa [Complex.intCast_re] using hs_re_pos)
  · intro hs_one
    rcases hs_strip with ⟨_, hs_re_lt⟩
    simp [hs_one] at hs_re_lt

end ExtendedRiemannHypothesis
