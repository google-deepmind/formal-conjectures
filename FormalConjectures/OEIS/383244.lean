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
# Primes from consecutive-prime gap products

For consecutive primes $q<r$, consider $qr(r-q)+1$. OEIS A383244 lists the prime values,
ordered by the index of $q$. The predicate $A$ records membership in this list. The list begins
$7,31,71,647,4003,6883,3527,\ldots$ and is not increasing in value.

*References:*
- [OEIS A383244](https://oeis.org/A383244)
- [OEIS A383242](https://oeis.org/A383242)
-/

@[expose] public section

namespace OeisA383244

/-- Two primes are consecutive when no prime lies strictly between them. -/
def ConsecutivePrimes (q r : ℕ) : Prop :=
  q.Prime ∧ r.Prime ∧ q < r ∧ ∀ t ∈ Finset.Ioo q r, ¬ t.Prime

instance (q r : ℕ) : Decidable (ConsecutivePrimes q r) := by
  unfold ConsecutivePrimes
  infer_instance

/-- Membership in the prime values $qr(r-q)+1$ for consecutive primes $q<r$. -/
def A (p : ℕ) : Prop :=
  p.Prime ∧ ∃ q r, ConsecutivePrimes q r ∧ p = q * r * (r - q) + 1

@[category test, AMS 11]
theorem a_7 : A 7 := by
  exact ⟨by decide, 2, 3, by decide, by decide⟩

@[category test, AMS 11]
theorem a_31 : A 31 := by
  exact ⟨by decide, 3, 5, by decide, by decide⟩

@[category test, AMS 11]
theorem a_71 : A 71 := by
  exact ⟨by decide, 5, 7, by decide, by decide⟩

@[category test, AMS 11]
theorem a_647 : A 647 := by
  exact ⟨by norm_num, 17, 19, by decide, by decide⟩

@[category test, AMS 11]
theorem a_4003 : A 4003 := by
  exact ⟨by norm_num, 23, 29, by decide, by decide⟩

@[category test, AMS 11]
theorem a_0 : ¬ A 0 := by
  intro h
  exact (by decide : ¬ Nat.Prime 0) h.1

@[category test, AMS 11]
theorem a_1 : ¬ A 1 := by
  intro h
  exact (by decide : ¬ Nat.Prime 1) h.1

@[category test, AMS 11]
theorem composite_gap_product : ¬ A 309 := by
  intro h
  exact (by norm_num : ¬ Nat.Prime 309) h.1

@[category test, AMS 11]
theorem two_five_not_consecutive : ¬ ConsecutivePrimes 2 5 := by decide

/-- Every member is prime. -/
@[category API, AMS 11]
theorem prime_of_a {p : ℕ} (h : A p) : p.Prime := h.1

/-- The subtraction in the gap of consecutive primes is positive. -/
@[category API, AMS 11]
theorem gap_pos {q r : ℕ} (h : ConsecutivePrimes q r) : 0 < r - q :=
  Nat.sub_pos_of_lt h.2.2.1

/-- "Conjecture: there are infinitely many such primes." -/
@[category research open, AMS 11]
theorem infinitely_many_gap_product_primes : {p : ℕ | A p}.Infinite := by
  sorry

end OeisA383244
