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

import FormalConjectures.ErdosProblems.«961»

/-!
# Erdős Problem 683

*References:*
- [erdosproblems.com/683](https://www.erdosproblems.com/683)
- [Er34] Erdős, Paul, A Theorem of Sylvester and Schur. J. London Math. Soc. (1934), 282--288.
- [Er55d] Erdős, P., On consecutive integers. Nieuw Arch. Wisk. (3) (1955), 124--128.
- [Er79d] Erdős, P., Some unconventional problems in number theory. Acta Math. Acad. Sci. Hungar. (1979), 71-80.
-/

namespace Erdos683

open Filter Real Erdos961

/--
Let $P(n, k)$ be the largest prime factor of $\binom{n}{k}$.
-/
def P (n k : ℕ) : ℕ := (n.choose k).primeFactors.sup id

/--
There exists $c > 0$ such that $P(n, k) > \min\{n-k+1, k^{1 + c}\}$ for all $0 < k < n$.}
-/
@[category research open, AMS 11]
theorem erdos_683 : answer(sorry) ↔
    (∃ c > (0 : ℝ), ∀ n k : ℕ, 0 < k ∧ k < n → P n k > min (n - k + 1 : ℝ) (k ^ (1 + c))) := by
  sorry

/--
Sylvester and Schur [Er34] proved that $P(n, k) > k$ for $k \le n/2$.
-/
@[category research solved, AMS 11]
theorem erdos_683.variant.sylvester_schur :
    ∀ n k : ℕ, 0 < k ∧ k ≤ n / 2 → P n k > k := by
  sorry

/--
Erdos [Er55d] improved this to $P(n, k) \gg k \log k $ for $k \le n/2$.
-/
@[category research solved, AMS 11]
theorem erdos_683.variant.erdos_log :
    ∃ c > 0, ∀ n k : ℕ, 0 < k ∧ k ≤ n / 2 → P n k > c * k * Real.log k := by
  sorry

/--
Standard heuristics suggest that $P(n, k) > e^{c\sqrt{k}}$ for some constant $c > 0$.
-/
@[category research open, AMS 11]
theorem erdos_683.variant.exp_sqrt :
    ∃ c > 0, ∀ n k : ℕ, 0 < k ∧ k ≤ n / 2 → P n k > Real.exp (c * Real.sqrt k) := by
  sorry

/--
Erdos 961 is equivalent to Erdos 683.
-/
@[category research solved, AMS 11]
theorem erdos_683_implies_erdos_961 :
    (∃ c₁ > (0 : ℝ), ∀ n k : ℕ, 0 < k ∧ k < n → P n k > min (n - k + 1 : ℝ) (k ^ (1 + c₁))) →
    (∃ c₂ > (0 : ℝ), ∀ᶠ k in atTop, f k < (log (k : ℝ)) ^ c₂) := by
  sorry

@[category research solved, AMS 11]
theorem erdos_961_implies_erdos_683 :
    (∃ c₂ > (0 : ℝ), ∀ᶠ k in atTop, f k < (log (k : ℝ)) ^ c₂) →
    (∃ c₁ > (0 : ℝ), ∀ n k : ℕ, 0 < k ∧ k < n → P n k > min (n - k + 1 : ℝ) (k ^ (1 + c₁))) := by
  sorry

end Erdos683
