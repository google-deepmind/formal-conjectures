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
# Erdős Problem 261

*References:*
 - [erdosproblems.com/261](https://www.erdosproblems.com/261)
 - [BoLo90] Borwein, Peter and Loring, Terry A., Some questions of Erdős and Graham on numbers
    of the form $\sum g_n/2^{g_n}$. Math. Comp. (1990), 377--394.
 - [TUZ20] Tengely, Szabolcs and Ulas, Maciej and Zygadlo, Jakub, On a Diophantine equation of
    Erdős and Graham. J. Number Theory (2020), 445--459.
-/

open scoped Cardinal

namespace Erdos261

/-- A natural number $n$ is said to have property `Erdos261_prop` if there exists $t \ge 2$ and
distinct integers $a_0, a_1, \ldots, a_t \ge 1$ such that
$n / 2^n = \sum_k a_k / 2^{a_k}$. -/
def Erdos261_prop (n : ℕ) : Prop := ∃ᵉ (t ≥ 2) (a : Fin t → ℕ), a.Injective ∧
  (1 ≤ a) ∧ n / (2 ^ n : ℚ) = ∑ k, (a k) / (2 ^ (a k) : ℚ)

/-- Borwein and Loring used the following example in [BoLO90] to show that there are infinitely
many natural numbers $n$ that satisfy `Erdos261_prop`. -/
@[category high_school, AMS 11]
theorem erdos_261.example (m : ℕ) :
    letI n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ) := by
  sorry

/-- As a corollary, there exist infinitely many numbers with the property. -/
@[category research solved, AMS 11]
theorem erdos_261.infinite : {n : ℕ | Erdos261_prop n}.Infinite := by
  sorry

/-- It is verified in [TUZ20] that all $n \le 10000$ satisfy `Erdos261_prop`. -/
@[category research solved, AMS 11]
theorem erdos_261.le_10000 {n : ℕ} (hn : n ≤ 10000) : Erdos261_prop n := by
  sorry

/-- Do all $n$ satisfy `Erdos261_prop`? -/
@[category research open, AMS 11]
theorem erdos_261.all : answer(sorry) ↔ ∀ n, Erdos261_prop n := by
  sorry

/-- Does there exist a rational `x` such that $x = \sum'_k (a(k)) / 2^{a(k)}$ has at least
$\mathfrak{c}$ many solutions? -/
@[category research open, AMS 11]
theorem erdos_261.rational : answer(sorry) ↔ ∃ x : ℚ,
    𝔠 ≤ #{a : ℕ → ℕ | Summable (fun k => (a k) / (2 ^ (a k) : ℚ)) ∧
    x = ∑' k, (a k) / (2 ^ (a k) : ℚ)} := by
  sorry

/-- Does there exist a rational `x` such that $x = \sum'_k (a(k)) / 2^{a(k)}$ has at least
$2$ solutions? -/
@[category research open, AMS 11]
theorem erdos_261.rational.weak : answer(sorry) ↔ ∃ x : ℚ,
    2 ≤ #{a : ℕ → ℕ | Summable (fun k => (a k) / (2 ^ (a k) : ℚ)) ∧
    x = ∑' k, (a k) / (2 ^ (a k) : ℚ)} := by
  sorry

end Erdos261
