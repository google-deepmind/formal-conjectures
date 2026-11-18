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
# McDaniel's Theorem on Smith Numbers and the Smith Brothers Problem

Coined by Albert Wilansky (1982), a base-$b$ *Smith number* ($b \ge 2$; `OEIS A006753` for $b = 10$)
is a composite integer $n$ whose base-$b$ digit sum matches the total base-$b$ digit sum across its
prime factors with multiplicity.

Wayne L. McDaniel (1987) proved that base-$10$ Smith numbers form an infinite set. Adjacent
base-$10$ Smith numbers $(n, n + 1)$—beginning at $(728, 729)$—form *Smith brothers* (the least
starting term of $k$ consecutive base-$10$ Smith numbers is `OEIS A059754`); whether infinitely many
pairs of Smith brothers exist remains open.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Smith_number)
- [OEIS A006753](https://oeis.org/A006753)
- [OEIS A059754](https://oeis.org/A059754)
- A. Wilansky, *Smith numbers*, Two-Year Coll. Math. J. **13** (1982), no. 1, 21.
- W. L. McDaniel, *The existence of infinitely many k-Smith numbers*, Fibonacci Quart. **25**
  (1987), no. 1, 76–80.
-/

@[expose] public section

namespace SmithNumber

/-- Base-$b$ digit sum of $n$. -/
def digitSum (b n : ℕ) : ℕ :=
  (Nat.digits b n).sum

/-- Total base-$b$ digit sum across the prime factors of $n$ counted with multiplicity. -/
def primeFactorsDigitSum (b n : ℕ) : ℕ :=
  (n.primeFactorsList.map (digitSum b)).sum

/-- Predicate asserting that $n$ is composite and its base-$b$ digit sum ($b \ge 2$) matches
`primeFactorsDigitSum b n`. -/
def IsSmithNumber (b n : ℕ) : Prop :=
  2 ≤ b ∧ n.Composite ∧ digitSum b n = primeFactorsDigitSum b n

instance (b n : ℕ) : Decidable (IsSmithNumber b n) :=
  inferInstanceAs (Decidable (2 ≤ b ∧ n.Composite ∧ digitSum b n = primeFactorsDigitSum b n))

/-- Checks the first two base-$10$ Smith numbers $4$ and $22$, the first Smith brother pair
$(728, 729)$, and the non-examples $2$ (prime) and $6$ ($6 \ne 2 + 3$). -/
@[category test, AMS 11]
theorem smallest_smith_numbers_witness :
    IsSmithNumber 10 4 ∧
      IsSmithNumber 10 22 ∧
      IsSmithNumber 10 728 ∧
      IsSmithNumber 10 729 ∧
      ¬ IsSmithNumber 10 2 ∧
      ¬ IsSmithNumber 10 6 := by
  decide +kernel

/-- Excludes degenerate bases $b = 0, 1$ and inputs $n = 0, 1$, and checks `digitSum 10 4 = 4`. -/
@[category test, AMS 11]
theorem smith_number_zero_one_and_four_sums :
    ¬ IsSmithNumber 0 4 ∧
      ¬ IsSmithNumber 1 4 ∧
      ¬ IsSmithNumber 10 0 ∧
      ¬ IsSmithNumber 10 1 ∧
      digitSum 10 4 = 4 ∧
      primeFactorsDigitSum 10 4 = 4 := by
  decide +kernel

/-- Every prime $p$ satisfies `primeFactorsDigitSum b p = digitSum b p`. -/
@[category API, AMS 11]
theorem primeFactorsDigitSum_of_prime (b : ℕ) {p : ℕ} (hp : p.Prime) :
    primeFactorsDigitSum b p = digitSum b p := by
  rw [primeFactorsDigitSum, Nat.primeFactorsList_prime hp, List.map_singleton, List.sum_singleton]

/-- No prime $p$ satisfies `IsSmithNumber b p`, since Smith numbers must be composite. -/
@[category API, AMS 11]
theorem not_isSmithNumber_of_prime (b : ℕ) {p : ℕ} (hp : p.Prime) :
    ¬ IsSmithNumber b p :=
  fun h => h.2.1.2 hp

/--
**McDaniel's Theorem (1987)**: Infinitely many base-$10$ Smith numbers exist.
-/
@[category research solved, AMS 11]
theorem mcdaniel_infinitely_many_smith_numbers :
    {n : ℕ | IsSmithNumber 10 n}.Infinite := by
  sorry

/--
Do infinitely many consecutive base-$10$ Smith-number pairs $(n, n + 1)$ (Smith brothers) exist?
-/
@[category research open, question, AMS 11]
theorem infinite_smith_brothers :
    {n : ℕ | IsSmithNumber 10 n ∧ IsSmithNumber 10 (n + 1)}.Infinite := by
  sorry

end SmithNumber
