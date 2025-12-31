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
# Erdős Problem 1074

*Reference:* [erdosproblems.com/1074](https://www.erdosproblems.com/1074)
-/

open scoped Nat

/-- The EHS numbers (after Erdős, Hardy, and Subbarao) are those $m\geq 1$ such that there
exists a prime $p\not\equiv 1\pmod{m}$ such that $m! + 1 \equiv 0\pmod{p}$.-/
abbrev Nat.EHSNumbers : Set ℕ := {m | 1 ≤ m ∧ ∃ p, p.Prime ∧ ¬p ≡ 1 [MOD m] ∧ p ∣ m ! + 1}

/-- The Pillai primes are those primes $p$ such that there exists an $m$ with
$p\not\equiv 1\pmod{m}$ such that $m! + 1 \equiv 0\pmod{p}$-/
abbrev Nat.PillaiPrimes : Set ℕ := {p | p.Prime ∧ ∃ m, ¬p ≡ 1 [MOD m] ∧ p ∣ m ! + 1}

namespace Erdos1074

open Nat

/-- Let $S$ be the set of all $m\geq 1$ such that there exists a prime $p\not\equiv 1\pmod{m}$ such
that $m! + 1 \equiv 0\pmod{p}$. Does
$$
  \lim\frac{|S\cap[1, x]|}{x}
$$
exist? -/
@[category research open, AMS 11]
theorem erdos_1074.part8_i_i : (∃ c, EHSNumbers.HasDensity c) ↔ answer(sorry) := by
  sorry

/-- Let $S$ be the set of all $m\geq 1$ such that there exists a prime $p\not\equiv 1\pmod{m}$ such
that $m! + 1 \equiv 0\pmod{p}$. What is
$$
  \lim\frac{|S\cap[1, x]|}{x}?
$$ -/
@[category research open, AMS 11]
theorem erdos_1074.part_i_ii : EHSNumbers.HasDensity answer(sorry) := by
  sorry

/-- Similarly, if $P$ is the set of all primes $p$ such that there exists an $m$ with
$p\not\equiv 1\pmod{m}$ such that $m! + 1 \equiv 0\pmod{p}$, then does
$$
  \lim\frac{|P\cap[1, x]|}{\pi(x)}
$$
exist? -/
@[category research open, AMS 11]
theorem erdos_1074.part_ii_i : (∃ c, PillaiPrimes.HasDensity c {p | p.Prime}) ↔ answer(sorry) := by
  sorry

/-- Similarly, if $P$ is the set of all primes $p$ such that there exists an $m$ with
$p\not\equiv 1\pmod{m}$ such that $m! + 1 \equiv 0\pmod{p}$, then what is
$$
  \lim\frac{|P\cap[1, x]|}{\pi(x)}?
$$ -/
@[category research open, AMS 11]
theorem erdos_1074.parts_ii_ii :
    PillaiPrimes.HasDensity answer(sorry) {p | p.Prime} := by
  sorry

/-- Pillai [Pi30] raised the question of whether there exist any primes in $P$. This was answered
by Chowla, who noted that, for example, $14! + 1 \equiv 18! + 1 \equiv 0 \pmod{23}$.-/
@[category test, AMS 11]
theorem erdos_1074.variants.mem_pillaiPrimes : 23 ∈ PillaiPrimes := by
  norm_num
  exact ⟨14, by decide⟩

/-- Erdős, Hardy, and Subbarao proved that $S$ is infinite. -/
@[category research solved, AMS 11]
theorem erdos_1074.variants.EHSNumbers_infinite : EHSNumbers.Infinite := by
  sorry

/-- Erdős, Hardy, and Subbarao proved that $P$ is infinite. -/
@[category research solved, AMS 11]
theorem erdos_1074.variants.PillaiPrimes_infinite : PillaiPrimes.Infinite := by
  sorry

/-- The sequence $S$ begins $8, 9, 13, 14, 15, 16, 17, ...$ -/
@[category test, AMS 11]
theorem erdos_1074.variants.EHSNumbers_init :
    nth EHSNumbers '' (Set.Icc 0 6) = {8, 9, 13, 14, 15, 16, 17} := by
  sorry

/-- The sequence $P$ begins $23, 29, 59, 61, 67, 71, ...$ -/
@[category test, AMS 11]
theorem erdos_1074.variants.PillaiPrimes_init :
    nth PillaiPrimes '' (Set.Icc 0 5) = {23, 29, 59, 61, 67, 71} := by
  sorry

/-- Regarding the first question, Hardy and Subbarao computed all EHS numbers up to $2^{10}$, and
write "...if this trend conditions we expect [the limit] to be around 0.5, if it exists." -/
@[category research open, AMS 11]
theorem erdos_1074.variants.EHSNumbers_one_half : EHSNumbers.HasDensity (1 / 2) := by
  sorry

end Erdos1074
