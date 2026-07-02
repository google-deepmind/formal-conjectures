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
# Erdős Problem 1109

*Reference:* [erdosproblems.com/1109](https://www.erdosproblems.com/1109)
-/

open Filter Asymptotics
open scoped Pointwise

namespace Erdos1109

/--
A finite set `A` has squarefree sumset if every element of `A + A` is squarefree.
-/
def IsSquarefreeSumset (A : Finset ℕ) : Prop :=
  ∀ n ∈ A + A, Squarefree n

/--
`f N` is the largest size of a subset `A ⊆ {1, ..., N}` such that every element
of `A + A` is squarefree.
-/
noncomputable def f (N : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsSquarefreeSumset A ∧ A.card = k}

/--
Let $f(N)$ be the size of the largest subset $A\subseteq \{1,\ldots,N\}$ such that
every $n\in A+A$ is squarefree. Is it true that $f(N)\leq N^{o(1)}$?

This formalizes the subpolynomial reading as `f(N) = O(N^ε)` for every `ε > 0`.
-/
@[category research open, AMS 5 11]
theorem erdos_1109 :
    answer(sorry) ↔ ∀ ε > (0 : ℝ),
      (fun N : ℕ => (f N : ℝ)) =O[atTop] fun N : ℕ => (N : ℝ) ^ ε := by
  sorry

/--
Is the stronger polylogarithmic bound $f(N) \leq (\log N)^{O(1)}$ true?
-/
@[category research open, AMS 5 11]
theorem erdos_1109.variants.polylog :
    answer(sorry) ↔ ∃ C > (0 : ℝ),
      (fun N : ℕ => (f N : ℝ)) =O[atTop] fun N : ℕ => (Real.log N) ^ C := by
  sorry

/--
Erdős and Sárközy proved the lower bound $\log N \ll f(N)$.
-/
@[category research solved, AMS 5 11]
theorem erdos_1109.variants.erdos_sarkozy_lower :
    (fun N : ℕ => Real.log N) =O[atTop] fun N : ℕ => (f N : ℝ) := by
  sorry

/--
Erdős and Sárközy proved the upper bound $f(N) \ll N^{3/4}\log N$.
-/
@[category research solved, AMS 5 11]
theorem erdos_1109.variants.erdos_sarkozy_upper :
    (fun N : ℕ => (f N : ℝ)) =O[atTop]
      fun N : ℕ => (N : ℝ) ^ ((3 : ℝ) / 4) * Real.log N := by
  sorry

/--
Konyagin improved the lower bound to
$\log\log N(\log N)^2 \ll f(N)$.
-/
@[category research solved, AMS 5 11]
theorem erdos_1109.variants.konyagin_lower :
    (fun N : ℕ => Real.log (Real.log N) * (Real.log N) ^ 2) =O[atTop]
      fun N : ℕ => (f N : ℝ) := by
  sorry

/--
Konyagin improved the upper bound to $f(N) \ll N^{11/15+o(1)}$.
-/
@[category research solved, AMS 5 11]
theorem erdos_1109.variants.konyagin_upper :
    ∀ ε > (0 : ℝ), (fun N : ℕ => (f N : ℝ)) =O[atTop]
      fun N : ℕ => (N : ℝ) ^ ((11 : ℝ) / 15 + ε) := by
  sorry

end Erdos1109
