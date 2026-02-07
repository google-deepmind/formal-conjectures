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
# Erdős Problem 535

*Reference:* [erdosproblems.com/535](https://www.erdosproblems.com/535)
-/

open Filter Real

namespace Erdos535

/-- `f r N` is the maximum size of a subset `A ⊆ {1,…,N}` such that no `r`-element
subset of `A` has constant pairwise GCD. -/
noncomputable def f (r N : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
    (∀ S ⊆ A, S.card = r →
      ¬∃ d, (S : Set ℕ).Pairwise fun a b => Nat.gcd a b = d) ∧
    A.card = k}

/--
Let $r \geq 3$, and let $f_r(N)$ denote the size of the largest subset of $\{1,\ldots,N\}$
such that no subset of size $r$ has the same pairwise greatest common divisor between all
elements. Erdős proved that $f_3(N) > N^{c/\log\log N}$ for some constant $c > 0$, and
conjectured this should also be an upper bound.

See also [536].
-/
@[category research open, AMS 5 11]
theorem erdos_535 : ∃ c > (0 : ℝ),
    ∀ᶠ (N : ℕ) in atTop,
      (f 3 N : ℝ) ≤ (N : ℝ) ^ (c / log (log (N : ℝ))) := by
  sorry

/-- Erdős proved that $f_3(N) > N^{c/\log\log N}$ for some constant $c > 0$. -/
@[category research solved, AMS 5 11]
theorem erdos_535.variants.lower_bound : ∃ c > (0 : ℝ),
    ∀ᶠ (N : ℕ) in atTop,
      (N : ℝ) ^ (c / log (log (N : ℝ))) ≤ (f 3 N : ℝ) := by
  sorry

/-- Abbott and Hanson improved Erdős's upper bound to $f_r(N) \leq N^{1/2+o(1)}$
for all $r \geq 3$. -/
@[category research solved, AMS 5 11]
theorem erdos_535.variants.abbott_hanson {r : ℕ} (hr : 3 ≤ r) :
    ∀ ε > (0 : ℝ), ∀ᶠ (N : ℕ) in atTop,
      (f r N : ℝ) ≤ (N : ℝ) ^ (1 / 2 + ε) := by
  sorry

end Erdos535
