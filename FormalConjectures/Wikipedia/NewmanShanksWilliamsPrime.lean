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
# Newman–Shanks–Williams primes

Define $(S_n)_{n \ge 0}$ (OEIS A001333) via $S_0 = 1$, $S_1 = 1$, and $S_{n+2} = 2 S_{n+1} + S_n$.
Odd-indexed entries
$$S_{2m + 1} = \frac{(1 + \sqrt{2})^{2m + 1} + (1 - \sqrt{2})^{2m + 1}}{2} \qquad (m \ge 0)$$
are Newman–Shanks–Williams (NSW) numbers (OEIS A002315), and prime terms among them are NSW primes
(OEIS A088165), beginning with $S_3 = 7$, $S_5 = 41$, $S_7 = 239$, and $S_{19} = 9369319$. Newman,
Shanks, and Williams (1980/1981) studied these primes while investigating finite simple groups
whose order is a square; whether infinitely many NSW primes exist remains open.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics#Prime_numbers)
- [Wikipedia: NSW prime](https://en.wikipedia.org/wiki/Newman%E2%80%93Shanks%E2%80%93Williams_prime)
- [OEIS A001333](https://oeis.org/A001333)
- [OEIS A002315](https://oeis.org/A002315)
- [OEIS A088165](https://oeis.org/A088165)
- M. Newman, D. Shanks, and H. C. Williams, *Simple groups of square order and an interesting
  sequence of primes*, Acta Arithmetica **38** (1980/1981), no. 2, 129–140,
  https://doi.org/10.4064/aa-38-2-129-140.
-/

@[expose] public section

namespace NewmanShanksWilliamsPrime

/-- Half-companion Pell recurrence $S_0 = 1$, $S_1 = 1$, $S_{n+2} = 2 S_{n+1} + S_n$. -/
def nswRecurrence : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 * nswRecurrence (n + 1) + nswRecurrence n

/-- The $m$-th Newman–Shanks–Williams number $S_{2m + 1}$. -/
def nswNumber (m : ℕ) : ℕ := nswRecurrence (2 * m + 1)

/-- Primality of $p$ combined with membership $p = S_{2m + 1}$ in the odd-indexed NSW sequence. -/
def IsNSWPrime (p : ℕ) : Prop :=
  p.Prime ∧ ∃ m : ℕ, nswNumber m = p

/-- Every term $S_n$ of `nswRecurrence` is at least $1$. -/
@[category API, AMS 11]
theorem one_le_nswRecurrence : ∀ n : ℕ, 1 ≤ nswRecurrence n
  | 0 => le_rfl
  | 1 => le_rfl
  | n + 2 => by
    have h1 := one_le_nswRecurrence (n + 1)
    have h0 := one_le_nswRecurrence n
    simp only [nswRecurrence]
    omega

/-- The sequence `nswRecurrence` is monotone on $\mathbb{N}$. -/
@[category API, AMS 11]
theorem monotone_nswRecurrence : Monotone nswRecurrence :=
  monotone_nat_of_le_succ fun
    | 0 => le_rfl
    | n + 1 => by
      simp only [nswRecurrence]
      omega

/-- Verifies `IsNSWPrime` on $7 = S_3$. -/
@[category test, AMS 11]
theorem isNSWPrime_seven : IsNSWPrime 7 :=
  ⟨by norm_num, 1, rfl⟩

/-- Verifies `IsNSWPrime` on $41 = S_5$. -/
@[category test, AMS 11]
theorem isNSWPrime_41 : IsNSWPrime 41 :=
  ⟨by norm_num, 2, rfl⟩

/-- Verifies `IsNSWPrime` on $239 = S_7$. -/
@[category test, AMS 11]
theorem isNSWPrime_239 : IsNSWPrime 239 :=
  ⟨by norm_num, 3, rfl⟩

/-- Excludes the initial odd-indexed term $S_1 = 1$, which is not prime. -/
@[category test, AMS 11]
theorem not_isNSWPrime_one : ¬ IsNSWPrime 1 :=
  fun h => Nat.not_prime_one h.1

/-- Confirms that the fifth NSW number $S_9 = 1393 = 7 \times 199$ is composite. -/
@[category test, AMS 11]
theorem not_prime_nswNumber_four : ¬ (nswNumber 4).Prime := by
  change ¬ Nat.Prime 1393
  norm_num

/-- Excludes the even-indexed prime $S_4 = 17$, which does not occur at any odd index. -/
@[category test, AMS 11]
theorem not_isNSWPrime_17 : ¬ IsNSWPrime 17 := by
  rintro ⟨_, m, hm⟩
  rcases m with _ | _ | m'
  · change 1 = 17 at hm; omega
  · change 7 = 17 at hm; omega
  · have h41 : 41 ≤ nswNumber (m' + 1 + 1) := by
      unfold nswNumber
      calc 41 = nswRecurrence 5 := rfl
        _ ≤ nswRecurrence (2 * (m' + 1 + 1) + 1) := monotone_nswRecurrence (by omega)
    omega

/--
Are infinitely many odd-indexed terms $S_{2m + 1}$ of the Newman–Shanks–Williams sequence prime?
-/
@[category research open, question, AMS 11]
theorem infinitely_many_nsw_primes : {p : ℕ | IsNSWPrime p}.Infinite := by
  sorry

end NewmanShanksWilliamsPrime
