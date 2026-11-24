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
# Base-$10$ Permutable Primes

A prime $p$ is a base-$10$ *permutable* (or *absolute*) prime ([OEIS A003459](https://oeis.org/A003459))
if every rearrangement of its decimal digits represents a prime. Apart from the single-digit primes
$\{2, 3, 5, 7\}$ and decimal repunit primes $R_n = (10^n - 1) / 9$ (`repunit10`) such as $R_2 = 11$,
the known examples are the seventeen primes
$\{13, 17, 31, 37, 71, 73, 79, 97, 113, 131, 199, 311, 337, 373, 733, 919, 991\}$.
It is conjectured that every base-$10$ permutable prime exceeding $991$ is a decimal repunit, and
that infinitely many base-$10$ permutable primes exist.

*References:*
- [Wikipedia: Permutable prime](https://en.wikipedia.org/wiki/Permutable_prime)
- [OEIS A003459](https://oeis.org/A003459)
- T. N. Bhargava and P. H. Doyle, *On the existence of absolute primes*, Mathematics Magazine
  **47** (1974), no. 4, 233, https://doi.org/10.1080/0025570X.1974.11976408.
-/

@[expose] public section

namespace PermutablePrime

/-- `p` is a base-$10$ permutable prime if `p` is prime and every permutation of its decimal digit
list represents a prime in base $10$. -/
def IsDecimalPermutablePrime (p : ℕ) : Prop :=
  p.Prime ∧ ∀ l ∈ (Nat.digits 10 p).permutations, (Nat.ofDigits 10 l).Prime

@[category test, AMS 11]
theorem isDecimalPermutablePrime_two : IsDecimalPermutablePrime 2 := by
  have h : Nat.digits 10 2 = [2] := by norm_num
  unfold IsDecimalPermutablePrime
  rw [h]
  simp only [List.mem_permutations, ← List.mem_permutations']
  simp [Nat.ofDigits]
  norm_num

@[category test, AMS 11]
theorem isDecimalPermutablePrime_13 : IsDecimalPermutablePrime 13 := by
  have h : Nat.digits 10 13 = [3, 1] := by norm_num
  unfold IsDecimalPermutablePrime
  rw [h]
  simp only [List.mem_permutations, ← List.mem_permutations']
  simp [Nat.ofDigits]
  norm_num

@[category test, AMS 11]
theorem isDecimalPermutablePrime_37 : IsDecimalPermutablePrime 37 := by
  have h : Nat.digits 10 37 = [7, 3] := by norm_num
  unfold IsDecimalPermutablePrime
  rw [h]
  simp only [List.mem_permutations, ← List.mem_permutations']
  simp [Nat.ofDigits]
  norm_num

@[category test, AMS 11]
theorem isDecimalPermutablePrime_113 : IsDecimalPermutablePrime 113 := by
  have h : Nat.digits 10 113 = [3, 1, 1] := by norm_num
  unfold IsDecimalPermutablePrime
  rw [h]
  simp only [List.mem_permutations, ← List.mem_permutations']
  simp [Nat.ofDigits]
  norm_num

@[category test, AMS 11]
theorem isDecimalPermutablePrime_991 : IsDecimalPermutablePrime 991 := by
  have h : Nat.digits 10 991 = [1, 9, 9] := by norm_num
  unfold IsDecimalPermutablePrime
  rw [h]
  simp only [List.mem_permutations, ← List.mem_permutations']
  simp [Nat.ofDigits]
  norm_num

@[category test, AMS 11]
theorem not_isDecimalPermutablePrime_19 : ¬ IsDecimalPermutablePrime 19 := by
  have h : Nat.digits 10 19 = [9, 1] := by norm_num
  unfold IsDecimalPermutablePrime
  rw [h]
  simp only [List.mem_permutations, ← List.mem_permutations']
  simp [Nat.ofDigits]
  norm_num

@[category test, AMS 11]
theorem not_isDecimalPermutablePrime_23 : ¬ IsDecimalPermutablePrime 23 := by
  have h : Nat.digits 10 23 = [3, 2] := by norm_num
  unfold IsDecimalPermutablePrime
  rw [h]
  simp only [List.mem_permutations, ← List.mem_permutations']
  simp [Nat.ofDigits]
  norm_num

@[category test, AMS 11]
theorem not_isDecimalPermutablePrime_103 : ¬ IsDecimalPermutablePrime 103 := by
  have h : Nat.digits 10 103 = [3, 0, 1] := by norm_num
  unfold IsDecimalPermutablePrime
  rw [h]
  simp only [List.mem_permutations, ← List.mem_permutations']
  simp [Nat.ofDigits]
  norm_num

/-- The decimal repunit $R_2 = 11$ satisfies `IsDecimalPermutablePrime`. -/
@[category test, AMS 11]
theorem isDecimalPermutablePrime_repunit10_two :
    IsDecimalPermutablePrime (repunit10 2) := by
  have hr2 : repunit10 2 = 11 := by decide
  rw [hr2]
  have hd : Nat.digits 10 11 = [1, 1] := by norm_num
  unfold IsDecimalPermutablePrime
  rw [hd]
  simp only [List.mem_permutations, ← List.mem_permutations']
  simp [Nat.ofDigits]
  norm_num

/-- The decimal repunit $R_3 = 111 = 3 \times 37$ is composite and not permutable prime. -/
@[category test, AMS 11]
theorem not_isDecimalPermutablePrime_repunit10_three :
    ¬ IsDecimalPermutablePrime (repunit10 3) := by
  have hr3 : repunit10 3 = 111 := by decide
  rw [hr3]
  intro h
  have := h.1
  norm_num at this

/--
Every base-$10$ permutable prime $p > 991$ is a decimal repunit $R_n = (10^n - 1) / 9$.
-/
@[category research open, AMS 11]
theorem permutable_prime_gt_991_is_repunit {p : ℕ} (hp : 991 < p)
    (hperm : IsDecimalPermutablePrime p) :
    ∃ n : ℕ, p = repunit10 n := by
  sorry

/--
Infinitely many base-$10$ permutable primes exist.
-/
@[category research open, AMS 11]
theorem infinitely_many_decimal_permutable_primes :
    {p : ℕ | IsDecimalPermutablePrime p}.Infinite := by
  sorry

end PermutablePrime
