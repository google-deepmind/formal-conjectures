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
# Erdős Problem 9

*Reference:* [erdosproblems.com/9](https://www.erdosproblems.com/9)
-/

/--
The set of odd numbers that cannot be expressed as a prime plus two powers of 2.
-/
def Erdos9A : Set ℕ := { n | Odd n ∧ ¬ ∃ (p k l : ℕ), (Nat.Prime p) ∧ n = p + 2 ^ k + 2 ^ l }


@[category test, AMS 5 11]
example : 1 ∈ Erdos9A := by
  constructor
  · decide
  · push_neg
    intro p k l hp
    linarith [Nat.Prime.two_le hp, @Nat.one_le_two_pow k, @Nat.one_le_two_pow l]

@[category test, AMS 5 11]
example : 3 ∈ Erdos9A := by
  constructor
  · decide
  · push_neg
    intro p k l hp
    linarith [Nat.Prime.two_le hp, @Nat.one_le_two_pow k, @Nat.one_le_two_pow l]

@[category test, AMS 5 11]
example : 5 ∉ Erdos9A := by
  unfold Erdos9A
  simp only [exists_and_left, not_exists, not_and, Set.mem_setOf_eq, not_forall, Classical.not_imp,
    Decidable.not_not]
  intro
  use 3, Nat.prime_three, 0, 0
  simp only [pow_zero, Nat.reduceAdd]


/--
The set is known to be infinite. In [Er77c] Erdős credits Schinzel with proving that there are
infinitely many odd integers not of this form, but gives no reference.

[Er77c] Erdős, P., _Problems and results on combinatorial number theory. III._.
-/
@[category research solved, AMS 5 11]
theorem erdos_9_infinite : Erdos9A.Infinite := by
  sorry

/--
Is the upper density of the set of odd numbers that cannot be expressed as a prime plus
two powers of 2 positive?
-/
@[category research open, AMS 5 11]
theorem erdos_9 : 0 < Erdos9A.upperDensity ↔ answer(sorry) := by
  sorry
