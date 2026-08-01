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

import FormalConjecturesUtil

/-!
# Green–Tao theorem

The Green–Tao theorem states that the sequence of prime numbers contains arbitrarily long
arithmetic progressions: for every positive integer $k$ there exist $a \in \mathbb{N}$ and
$d > 0$ such that
$$a,\ a+d,\ a+2d,\ \ldots,\ a+(k-1)d$$
are all prime.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Green%E2%80%93Tao_theorem)
- B. Green and T. Tao, *The primes contain arbitrarily long arithmetic progressions*,
  Ann. of Math. (2) 167 (2008), no. 2, 481–547
-/

namespace GreenTao

/--
A $k$-term arithmetic progression of natural numbers with first term $a$ and common difference
$d > 0$ consists entirely of primes.
-/
def IsPrimeAP (k a d : ℕ) : Prop :=
  0 < d ∧ ∀ i < k, Nat.Prime (a + i * d)

/--
**Green–Tao theorem.** For every positive integer $k$ there exists a $k$-term arithmetic
progression of prime numbers.
-/
@[category research solved, AMS 5 11]
theorem green_tao_theorem (k : ℕ) (hk : 0 < k) :
    ∃ a d : ℕ, IsPrimeAP k a d := by
  sorry

/-- Unpacked form of the Green–Tao theorem without the auxiliary `IsPrimeAP` definition. -/
@[category API, AMS 5 11]
theorem green_tao_theorem.unpacked (k : ℕ) (hk : 0 < k) :
    ∃ a d : ℕ, 0 < d ∧ ∀ i < k, Nat.Prime (a + i * d) := by
  obtain ⟨a, d, hd, h⟩ := green_tao_theorem k hk
  exact ⟨a, d, hd, h⟩

/-- Length $1$: any prime is a trivial one-term arithmetic progression. -/
@[category test, AMS 5 11]
theorem isPrimeAP_one_of_prime {a : ℕ} (ha : Nat.Prime a) : IsPrimeAP 1 a 1 := by
  refine ⟨by norm_num, ?_⟩
  intro i hi
  have : i = 0 := by omega
  simpa [this] using ha

/-- Length $2$: the primes $3,5$ form a progression with difference $2$. -/
@[category test, AMS 5 11]
theorem isPrimeAP_three_five : IsPrimeAP 2 3 2 := by
  refine ⟨by norm_num, ?_⟩
  intro i hi
  interval_cases i <;> norm_num

/-- Length $3$: the primes $3,5,7$ form a progression with difference $2$. -/
@[category test, AMS 5 11]
theorem isPrimeAP_three_five_seven : IsPrimeAP 3 3 2 := by
  refine ⟨by norm_num, ?_⟩
  intro i hi
  interval_cases i <;> norm_num

/-- A non-example: $8,10$ is an arithmetic progression of length $2$ but not of primes. -/
@[category test, AMS 5 11]
theorem not_isPrimeAP_eight_ten : ¬ IsPrimeAP 2 8 2 := by
  intro h
  have h8 := h.2 0 (by norm_num)
  norm_num at h8

end GreenTao
