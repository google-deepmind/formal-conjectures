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

import FormalConjecturesUtil

/-!
# Erdős Problem 470

*Reference:* [erdosproblems.com/470](https://www.erdosproblems.com/470)
-/

namespace Erdos470

/--
Primitive weird numbers are weird numbers such that no proper divisor of $n$ are weird.
-/
def PrimitiveWeird (n : ℕ) := n.Weird ∧ ∀ d ∈ n.properDivisors, ¬d.Weird

/--
The abundancy index is the sum of the divisors of $n$ divided by $n$.
-/
def AbundancyIndex (n : ℕ) : ℚ := (∑ d ∈ n.divisors, d) / n

/--
Are there any odd weird numbers?
-/
@[category research open, AMS 11]
theorem erdos_470.parts.i : answer(sorry) ↔ ∃ n : ℕ, n.Weird ∧ Odd n := by
  sorry

/--
Are there infinitely many primitive weird numbers?
-/
@[category research open, AMS 11]
theorem erdos_470.parts.ii : answer(sorry) ↔ Set.Infinite PrimitiveWeird := by
  sorry

/--
Benkoski and Erdős [BeEr74](https://mathscinet.ams.org/mathscinet/relay-station?mr=347726) proved
that the set of weird numbers has positive density.
-/
@[category research solved, AMS 11]
theorem erdos_470.variants.weird_pos_density : {n : ℕ | n.Weird}.HasPosDensity := by
  sorry

/--
The smallest weird number is 70.
-/
@[category textbook, AMS 11]
theorem erdos_470.variants.smallest_weird_eq_70 : (∀ n < 70, ¬n.Weird) ∧ (70).Weird := by
  refine ⟨?_, Nat.weird_seventy⟩
  rintro n hn ⟨ha, hnp⟩
  unfold Nat.Abundant at ha
  apply hnp
  -- For non-abundant `n`, `ha` is contradictory; for each abundant `n < 70`, exhibit an explicit
  -- subset of its proper divisors summing to `n` (so `n` is pseudoperfect, hence not weird).
  interval_cases n <;>
    first
    | exact absurd ha (by decide)
    | exact ⟨by decide, ({2, 4, 6} : Finset ℕ), by decide, by decide⟩
    | exact ⟨by decide, ({3, 6, 9} : Finset ℕ), by decide, by decide⟩
    | exact ⟨by decide, ({1, 4, 5, 10} : Finset ℕ), by decide, by decide⟩
    | exact ⟨by decide, ({4, 8, 12} : Finset ℕ), by decide, by decide⟩
    | exact ⟨by decide, ({5, 10, 15} : Finset ℕ), by decide, by decide⟩
    | exact ⟨by decide, ({6, 12, 18} : Finset ℕ), by decide, by decide⟩
    | exact ⟨by decide, ({2, 8, 10, 20} : Finset ℕ), by decide, by decide⟩
    | exact ⟨by decide, ({7, 14, 21} : Finset ℕ), by decide, by decide⟩
    | exact ⟨by decide, ({8, 16, 24} : Finset ℕ), by decide, by decide⟩
    | exact ⟨by decide, ({9, 18, 27} : Finset ℕ), by decide, by decide⟩
    | exact ⟨by decide, ({2, 4, 8, 14, 28} : Finset ℕ), by decide, by decide⟩
    | exact ⟨by decide, ({10, 20, 30} : Finset ℕ), by decide, by decide⟩
    | exact ⟨by decide, ({11, 22, 33} : Finset ℕ), by decide, by decide⟩

/--
Melfi [Me15](https://mathscinet.ams.org/mathscinet/relay-station?mr=3276337) has proved that there
are infinitely many primitive weird numbers, conditional on the fact that
$p_{n+1} - p_n < \frac{1}{10} \sqrt{p_n}$ for all large $n$, which in turn would follow from
well-known conjectures concerning prime gaps.
-/
@[category research solved, AMS 11]
theorem erdos_470.variants.prime_gap_imp_inf_prim_weird :
    (∀ᶠ n in Filter.atTop, primeGap n < √ (n.nth Nat.Prime) / 10) →
      Set.Infinite PrimitiveWeird := by
  sorry

/--
Fang [Fa22](https://arxiv.org/abs/2207.12906) has shown there are no odd weird numbers below $10^{21}$.
-/
@[category research solved, AMS 11]
theorem erdos_470.variants.odd_weird_10_pow_21 : ∀ n < 10 ^ 21, Odd n → ¬n.Weird := by
  sorry

/--
Liddy and Riedl [LiRi18](https://ideaexchange.uakron.edu/honors_research_projects/728/) have shown
that an odd weird number must have at least 6 prime divisors.
-/
@[category research solved, AMS 11]
theorem erdos_470.variants.odd_weird_prime_div :
    ∀ n : ℕ, Odd n → n.Weird → 6 ≤ {m | m ∈ n.divisors ∧ m.Prime}.ncard := by
  sorry

/--
If there are no odd weird numbers then every weird number has abundancy index < 4.
-/
@[category research solved, AMS 11]
theorem erdos_470.variants.abundancy_index :
    (∀ n : ℕ, n.Weird → ¬Odd n) → ∀ n, n.Weird → AbundancyIndex n < 4 := by
  sorry

end Erdos470
