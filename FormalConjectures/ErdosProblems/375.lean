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
import FormalConjectures.Wikipedia.LegendreConjecture

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

/-- This is a proposition saying that for any `n ≥ 1` and any `k`, if `n + 1, ..., n + k` are all
composite, then there are distinct primes `p₁, ... pₖ` such that `pᵢ ∣ n + i` for all `1 ≤ i ≤ k`.
-/
def Erdos375 : Prop := ∀ n ≥ 1, ∀ k, (∀ i < k, ¬ (n + i + 1).Prime) →
    ∃ p : Fin k → ℕ, p.Injective ∧ ∀ i, (p i).Prime ∧ p i ∣ n + i + 1

/-- Is `Erdos375` true? -/
@[category research open, AMS 11]
theorem erdos_375 : answer(sorry) ↔ Erdos375 := by
  sorry

/-- If `Erdos375` is true, then `(n + 1).nth Prime - n.nth Prime < (n.nth Prime) ^ (1 / 2 - c)`
for some `c > 0`. -/
@[category research solved, AMS 11]
theorem erdos_375.bounded_gap : Erdos375 →
    ∃ c > 0, ∀ᶠ n in atTop, (n + 1).nth Nat.Prime - n.nth Nat.Prime
    < (n.nth Nat.Prime : ℝ) ^ (1 / (2 : ℝ) - c) := by
  sorry

/-- In particular, if `Erdos375` is true, then it resolves Legendre's conjecture.-/
@[category research solved, AMS 11]
theorem erdos_375.legendre : Erdos375 →
    (∀ᶠ n in atTop, ∃ p ∈ Set.Ioo (n ^ 2) ((n + 1) ^ 2), Nat.Prime p) :=
  fun hp => LegendreConjecture.bounded_gap_legendre (erdos_375.bounded_gap hp)

/-- It is easy to see that for any `n ≥ 1` and `k ≤ 2`, if `n + 1, ..., n + k` are all composite,
then there are distinct primes `p₁, ... pₖ` such that `pᵢ ∣ n + i` for all `1 ≤ i ≤ k`. -/
@[category research solved, AMS 11]
theorem erdos_375.le_two : ∀ n ≥ 1, ∀ k ≤ 2, (∀ i < k, ¬ (n + i + 1).Prime) →
    ∃ p : Fin k → ℕ, p.Injective ∧ ∀ i, (p i).Prime ∧ p i ∣ n + i + 1 := by
  intro n hn k hk
  interval_cases k <;> intro h
  · simp_all; intro; grind
  · choose! p hp using (n + 1).exists_prime_and_dvd (by linarith)
    exact ⟨fun x => p, fun x => by grind, fun i => by simpa using hp⟩
  · choose! p hp using (fun i : Fin 2 => (n + i + 1).exists_prime_and_dvd (by linarith))
    refine ⟨p, fun x y hxy => ?_, hp⟩
    by_contra! hr
    wlog hq : x < y
    · exact this n hn k hk h p hp y x hxy.symm hr.symm (by grind)
    · have hy : y = x + 1 := by grind
      have := hy ▸ Nat.dvd_sub (hp y).2 (hxy ▸ (hp x).2)
      have := (hp 1).1
      simp_all [Nat.not_prime_one]

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
