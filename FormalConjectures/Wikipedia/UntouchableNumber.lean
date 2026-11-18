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
module

public import FormalConjecturesUtil

/-!
# Untouchable Numbers

A natural number $m$ is *untouchable* (or *nonaliquot*, OEIS A005114) when it lies outside the
range of the proper-divisor sum $s(n) = \sigma(n) - n = \sum_{d \mid n,\, d < n} d$; examples begin
at $2, 5$, and $52$.

Erdős (1973) proved that untouchable integers have positive lower asymptotic density (see also
`Erdos418.erdos_418.variants.sigma` in `FormalConjectures.ErdosProblems.«418»`), and Chen and Zhao
(2011) proved that at least $0.06 x + o(x)$ even integers below $x$ are untouchable, giving lower
asymptotic density at least $0.06$. Meanwhile, $5$ is conjectured to be the sole odd untouchable
integer: writing an even integer $2k > 6$ as $p + q$ for distinct primes $p \ne q$ gives
$s(p q) = 1 + p + q = 2k + 1$, ruling out every odd integer above $7$.

*References:*
- [Wikipedia: Untouchable number](https://en.wikipedia.org/wiki/Untouchable_number)
- [OEIS A005114](https://oeis.org/A005114)
- P. Erdős (1973), *Elem. Math.* **28**, 83–86.
- Y.-G. Chen and Q.-Q. Zhao (2011), *Publ. Math. Debrecen*, vol. 78, 439–442.
- R. K. Guy (2004), Section B10.
-/

@[expose] public section

namespace UntouchableNumber

/-- Every integer $n \ge 30$ is either prime (proper-divisor sum $1$) or composite with a proper
divisor at least $6$ (proper-divisor sum at least $6$). -/
@[category API, AMS 11]
theorem properDivisors_sum_eq_one_or_ge_six_of_ge_thirty {n : ℕ} (hn : 30 ≤ n) :
    ∑ d ∈ n.properDivisors, d = 1 ∨ 6 ≤ ∑ d ∈ n.properDivisors, d := by
  by_cases hp : n.Prime
  · exact Or.inl (by simp [hp.properDivisors])
  · right
    set p := n.minFac
    have hp_prime : p.Prime := Nat.minFac_prime (by omega)
    have hp_two : 2 ≤ p := hp_prime.two_le
    obtain ⟨q, hnq⟩ := Nat.minFac_dvd n
    have hq_two : 2 ≤ q := by
      rcases q with _ | _ | q
      · omega
      · simp at hnq; exact absurd (hnq ▸ hp_prime) hp
      · omega
    have hmax : 6 ≤ max p q := by
      by_contra!
      nlinarith [le_max_left p q, le_max_right p q]
    have hmem : max p q ∈ n.properDivisors := by
      rcases max_choice p q with h | h <;> rw [h, Nat.mem_properDivisors]
      · exact ⟨⟨q, hnq⟩, by nlinarith⟩
      · exact ⟨⟨p, by linarith⟩, by nlinarith⟩
    exact hmax.trans (Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hmem)

/-- None of $0, 1, 3, 4, 7$ is untouchable ($0 = s(1)$, $1 = s(2)$, $3 = s(4)$, $4 = s(9)$,
$7 = s(8)$). -/
@[category test, AMS 11]
theorem not_isUntouchable_small_values :
    ¬ Nat.IsUntouchable 0 ∧ ¬ Nat.IsUntouchable 1 ∧ ¬ Nat.IsUntouchable 3 ∧
      ¬ Nat.IsUntouchable 4 ∧ ¬ Nat.IsUntouchable 7 :=
  ⟨Nat.not_isUntouchable_zero, Nat.not_isUntouchable_one,
    fun h => h ⟨4, by decide⟩, fun h => h ⟨9, by decide⟩, fun h => h ⟨8, by decide⟩⟩

/-- $2$ is untouchable. -/
@[category test, AMS 11]
theorem isUntouchable_two : Nat.IsUntouchable 2 := by
  rintro ⟨n, hsum⟩
  by_cases hn30 : n < 30
  · interval_cases n <;> revert hsum <;> decide
  · rcases properDivisors_sum_eq_one_or_ge_six_of_ge_thirty (Nat.not_lt.mp hn30) with h1 | h6 <;>
      omega

/-- $5$ is untouchable. -/
@[category test, AMS 11]
theorem isUntouchable_five : Nat.IsUntouchable 5 := by
  rintro ⟨n, hsum⟩
  by_cases hn30 : n < 30
  · interval_cases n <;> revert hsum <;> decide
  · rcases properDivisors_sum_eq_one_or_ge_six_of_ge_thirty (Nat.not_lt.mp hn30) with h1 | h6 <;>
      omega

/-- **Erdős (1973); Chen–Zhao (2011):** Untouchable integers have lower asymptotic density at least
$0.06$ (Chen and Zhao prove that at least $0.06 x + o(x)$ even integers below $x$ are nonaliquot;
compare `Erdos418.erdos_418.variants.sigma`). -/
@[category research solved, AMS 11]
theorem chen_zhao_untouchable_lower_density :
    (6 / 100 : ℝ) ≤ Set.lowerDensity {m : ℕ | m.IsUntouchable} := by
  sorry

/-- **Unique Odd Untouchable Conjecture:** Among odd integers, $5$ is the unique untouchable
value. -/
@[category research open, AMS 11]
theorem unique_odd_untouchable_conjecture {m : ℕ} (hodd : Odd m) :
    m.IsUntouchable ↔ m = 5 := by
  sorry

end UntouchableNumber
