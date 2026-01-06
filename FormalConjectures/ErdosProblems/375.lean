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
# Erdős Problem 375

*References:*
 - [erdosproblems.com/375](https://www.erdosproblems.com/375)
 - [ErGr80] Erdős, P. and Graham, R., Old and new problems and results in combinatorial number
    theory. Monographies de L'Enseignement Mathematique (1980).
 - [RST75] Ramachandra, K. and Shorey, T. N. and Tijdeman, R., On Grimm's problem relating to
    factorisation of a block of consecutive integers. J. Reine Angew. Math. (1975), 109-124.
 -
-/

open Set Filter Topology Asymptotics

namespace Erdos375

/-- Is it true that for any `n ≥ 1` and any `k`, if `n + 1, ..., n + k` are all composite, then
there are distinct primes `p₁, ... pₖ` such that `pᵢ ∣ n + i` for all `1 ≤ i ≤ k`? -/
@[category research open, AMS 11]
theorem erdos_375 : answer(sorry) ↔ ∀ n ≥ 1, ∀ k, (∀ i < k, ¬ (n + i + 1).Prime) →
    ∃ p : Fin k → ℕ, p.Injective ∧ ∀ i, (p i).Prime ∧ p i ∣ n + i + 1 := by
  sorry

/-- If `erdos_375` is true, then `(n + 1).nth Prime - n.nth Prime < (n.nth Prime) ^ (1 / 2 - c)`
for some `c > 0`. In particular, this resolves Legendre's conjecture. -/
@[category research solved, AMS 11]
theorem erdos_375.legendre : (∀ n ≥ 1, ∀ k, (∀ i < k, ¬ (n + i + 1).Prime) →
    ∃ p : Fin k → ℕ, p.Injective ∧ ∀ i, (p i).Prime ∧ p i ∣ n + i + 1) →
    ∃ c > 0, ∀ n, (n + 1).nth Prime - n.nth Prime < (n.nth Prime : ℝ) ^ (1 / (2 : ℝ) - c) := by
  sorry

/-- For any `n ≥ 1` and `k ≤ 2`, if `n + 1, ..., n + k` are all composite, then
there are distinct primes `p₁, ... pₖ` such that `pᵢ ∣ n + i` for all `1 ≤ i ≤ k`. -/
@[category research solved, AMS 11]
theorem erdos_375.le_two : ∀ n ≥ 1, ∀ k ≤ 2, (∀ i < k, ¬ (n + i + 1).Prime) →
    ∃ p : Fin k → ℕ, p.Injective ∧ ∀ i, (p i).Prime ∧ p i ∣ n + i + 1 := by
  sorry

/-- There exists a constant `c > 0` such that for all `n` large enough, if
`k < c * (log n / (log (log n))) ^ 3 → (∀ i < k, ¬ (n + i + 1).Prime)`, then
there are distinct primes `p₁, ... pₖ` such that `pᵢ ∣ n + i` for all `1 ≤ i ≤ k`. This is proved
in [RST75]. -/
@[category research solved, AMS 11]
theorem erdos_375.log : ∃ c > 0, ∀ n k : ℕ,
    k < c * (Real.log n / (Real.log (Real.log n))) ^ 3 → (∀ i < k, ¬ (n + i + 1).Prime) →
    ∃ p : Fin k → ℕ, p.Injective ∧ ∀ i, (p i).Prime ∧ p i ∣ n + i + 1 := by
  sorry

end Erdos375
