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
# Fortunate numbers

A *Fortunate number* `F n` is the smallest integer `m > 1` such that `pr n + m` is
prime, where `pr n` denotes the primorial: the product of the first `n` prime numbers.

*Fortune's conjecture* states that no Fortunate number is composite, equivalently,
that every Fortunate number is prime.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Fortunate_number)
- [OEIS A005235](https://oeis.org/A005235)
-/

namespace FortunateNumber

/-- The primorial `pr n` is the product of the first `n` prime numbers, `p₀ p₁ ⋯ pₙ₋₁`
(note the `0`-indexing: `Nat.nth Nat.Prime 0 = 2`). -/
noncomputable def primorial (n : ℕ) : ℕ := ∏ i ∈ Finset.range n, i.nth Nat.Prime

/-- For every `P`, there is some `m > 1` with `P + m` prime: pick a prime `p ≥ P + 2`
(Euclid's theorem) and take `m = p - P`. This guarantees `fortuneNumber` is well-defined. -/
@[category API, AMS 11]
theorem exists_prime_add (P : ℕ) : ∃ m, 1 < m ∧ (P + m).Prime := by
  obtain ⟨p, hp, hpp⟩ := Nat.exists_infinite_primes (P + 2)
  exact ⟨p - P, by omega, by rwa [Nat.add_sub_cancel' (by omega : P ≤ p)]⟩

/-- The `n`-th *Fortunate number* is the smallest `m > 1` such that `primorial n + m`
is prime. -/
noncomputable def fortuneNumber (n : ℕ) : ℕ :=
  Nat.find (exists_prime_add (primorial n))

/-- Rewriting lemma: reduces `fortuneNumber n` to a `Nat.find` over a concrete
primorial value `P`, enabling evaluation of small cases. -/
@[category API, AMS 11]
theorem fortuneNumber_eq_find (n P : ℕ) (hP : primorial n = P) :
    fortuneNumber n = Nat.find (exists_prime_add P) := by
  subst hP; rfl

@[category API, AMS 11]
theorem nth_prime_zero : Nat.nth Nat.Prime 0 = 2 := by
  have h := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 2 by norm_num)
  rwa [show Nat.count Nat.Prime 2 = 0 by decide] at h

@[category API, AMS 11]
theorem nth_prime_one : Nat.nth Nat.Prime 1 = 3 := by
  have h := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 3 by norm_num)
  rwa [show Nat.count Nat.Prime 3 = 1 by decide] at h

@[category API, AMS 11]
theorem nth_prime_two : Nat.nth Nat.Prime 2 = 5 := by
  have h := Nat.nth_count (p := Nat.Prime) (show Nat.Prime 5 by norm_num)
  rwa [show Nat.count Nat.Prime 5 = 2 by decide] at h

@[category API, AMS 11]
theorem primorial_one : primorial 1 = 2 := by
  rw [primorial, Finset.prod_range_one, nth_prime_zero]

@[category API, AMS 11]
theorem primorial_two : primorial 2 = 6 := by
  rw [primorial, Finset.prod_range_succ, Finset.prod_range_one, nth_prime_zero, nth_prime_one]
  norm_num

@[category API, AMS 11]
theorem primorial_three : primorial 3 = 30 := by
  rw [primorial, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_one,
    nth_prime_zero, nth_prime_one, nth_prime_two]
  norm_num

/--
**Fortune's conjecture.** Every Fortunate number is prime.
-/
@[category research open, AMS 11]
theorem fortune_conjecture : ∀ n, (fortuneNumber n).Prime := by
  sorry

/-- `F 1 = 3`, since `primorial 1 = 2` and `2 + 3 = 5` is the least prime shift `> 1`. -/
@[category test, AMS 11]
theorem fortuneNumber_one : fortuneNumber 1 = 3 := by
  rw [fortuneNumber_eq_find 1 2 primorial_one, Nat.find_eq_iff]; decide

/-- `F 2 = 5`, since `primorial 2 = 6` and `6 + 5 = 11` is the least prime shift `> 1`. -/
@[category test, AMS 11]
theorem fortuneNumber_two : fortuneNumber 2 = 5 := by
  rw [fortuneNumber_eq_find 2 6 primorial_two, Nat.find_eq_iff]; decide

/-- `F 3 = 7`, since `primorial 3 = 30` and `30 + 7 = 37` is the least prime shift `> 1`. -/
@[category test, AMS 11]
theorem fortuneNumber_three : fortuneNumber 3 = 7 := by
  rw [fortuneNumber_eq_find 3 30 primorial_three, Nat.find_eq_iff]; decide

end FortunateNumber
