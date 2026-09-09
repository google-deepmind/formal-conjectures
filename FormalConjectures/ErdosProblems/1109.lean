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

import FormalConjecturesUtil

/-!
# Erdős Problem 1109

*References:*
- [erdosproblems.com/1109](https://www.erdosproblems.com/1109)
- [ErSa87] P. Erdős and A. Sárközy, *On divisibility properties of integers of the form
  $a+a'$*, Acta Math. Hungar. (1987), 117--122.
- [Gy01] Katalin Gyarmati, *On divisibility properties of integers of the form $ab+1$*,
  Period. Math. Hungar. (2001), 71--79.
- [Ko04] S. V. Konyagin, *Problems of the set of square-free numbers*,
  Izv. Ross. Akad. Nauk Ser. Mat. (2004), 63--90.
- [Sa92c] G. N. Sárközy, *On a problem of P. Erdős*, Acta Math. Hungar.
  (1992), 271--282.
-/

open Filter Asymptotics
open scoped Pointwise

namespace Erdos1109

/--
`f N` is the largest size of a subset `A ⊆ {1, ..., N}` such that every element
of `A + A` is squarefree.
-/
noncomputable def f (N : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℕ,
    A ⊆ Finset.Icc 1 N ∧ (∀ n ∈ A + A, Squarefree n) ∧ A.card = k}

/--
Let $f(N)$ be the size of the largest subset $A\subseteq \{1,\ldots,N\}$ such that
every $n\in A+A$ is squarefree. Estimate $f(N)$. In particular, is it true that
$f(N)\leq N^{o(1)}$, or even $f(N) \leq (\log N)^{O(1)}$?

This theorem formalizes the subpolynomial bound as `f(N) = O(N^ε)` for every `ε > 0`.
-/
@[category research open, AMS 5 11]
theorem erdos_1109 :
    answer(sorry) ↔ ∀ ε > (0 : ℝ),
      (fun N : ℕ => (f N : ℝ)) ≪ fun N : ℕ => (N : ℝ) ^ ε := by
  sorry

/--
Is the stronger polylogarithmic bound $f(N) \leq (\log N)^{O(1)}$ true?
-/
@[category research open, AMS 5 11]
theorem erdos_1109.variants.polylog :
    answer(sorry) ↔ ∃ C > (0 : ℝ),
      (fun N : ℕ => (f N : ℝ)) ≪ fun N : ℕ => (Real.log N) ^ C := by
  sorry

/--
Erdős and Sárközy [ErSa87] proved the lower bound $\log N \ll f(N)$.
-/
@[category research solved, AMS 5 11]
theorem erdos_1109.variants.erdos_sarkozy_lower :
    (fun N : ℕ => Real.log N) ≪ fun N : ℕ => (f N : ℝ) := by
  sorry

/--
Erdős and Sárközy [ErSa87] proved the upper bound $f(N) \ll N^{3/4}\log N$.
-/
@[category research solved, AMS 5 11]
theorem erdos_1109.variants.erdos_sarkozy_upper :
    (fun N : ℕ => (f N : ℝ)) ≪
      fun N : ℕ => (N : ℝ) ^ ((3 : ℝ) / 4) * Real.log N := by
  sorry

/--
Konyagin [Ko04] improved the lower bound to
$\log\log N(\log N)^2 \ll f(N)$.
-/
@[category research solved, AMS 5 11]
theorem erdos_1109.variants.konyagin_lower :
    (fun N : ℕ => Real.log (Real.log N) * (Real.log N) ^ 2) ≪
      fun N : ℕ => (f N : ℝ) := by
  sorry

/--
Konyagin [Ko04] improved the upper bound to $f(N) \ll N^{11/15+o(1)}$.
-/
@[category research solved, AMS 5 11]
theorem erdos_1109.variants.konyagin_upper :
    ∀ ε > (0 : ℝ), (fun N : ℕ => (f N : ℝ)) ≪
      fun N : ℕ => (N : ℝ) ^ ((11 : ℝ) / 15 + ε) := by
  sorry

end Erdos1109
