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
public import FormalConjectures.Wikipedia.RepunitPrime

/-!
# Base-$10$ Permutable Primes

A prime $p$ is a base-$10$ *permutable* (or *absolute*) prime (`A003459`) if every rearrangement of
its decimal digits represents a prime. Apart from the single-digit primes $\{2, 3, 5, 7\}$ and
decimal repunit primes $R_n = (10^n - 1) / 9$ (`RepunitPrime.repunit10`) such as $R_2 = 11$, the
known examples are the seventeen primes
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

/-- Checks positive witnesses $2, 13, 37, 113, 991$ and negative witnesses $19, 23, 103$. -/
@[category test, AMS 11]
theorem isDecimalPermutablePrime_small_checks :
    IsDecimalPermutablePrime 2 ∧ IsDecimalPermutablePrime 13 ∧ IsDecimalPermutablePrime 37 ∧
      IsDecimalPermutablePrime 113 ∧ IsDecimalPermutablePrime 991 ∧
      ¬ IsDecimalPermutablePrime 19 ∧ ¬ IsDecimalPermutablePrime 23 ∧
      ¬ IsDecimalPermutablePrime 103 := by
  have h2 : Nat.digits 10 2 = [2] := by norm_num
  have h13 : Nat.digits 10 13 = [3, 1] := by norm_num
  have h37 : Nat.digits 10 37 = [7, 3] := by norm_num
  have h113 : Nat.digits 10 113 = [3, 1, 1] := by norm_num
  have h991 : Nat.digits 10 991 = [1, 9, 9] := by norm_num
  have h19 : Nat.digits 10 19 = [9, 1] := by norm_num
  have h23 : Nat.digits 10 23 = [3, 2] := by norm_num
  have h103 : Nat.digits 10 103 = [3, 0, 1] := by norm_num
  unfold IsDecimalPermutablePrime
  rw [h2, h13, h37, h113, h991, h19, h23, h103]
  simp only [List.mem_permutations, ← List.mem_permutations']
  simp [Nat.ofDigits]
  norm_num

/-- Checks small decimal repunits: $R_2 = 11$ satisfies `IsDecimalPermutablePrime`, whereas
$R_3 = 111 = 3 \times 37$ does not. -/
@[category test, AMS 11]
theorem repunit10_two_and_three_permutable :
    IsDecimalPermutablePrime (RepunitPrime.repunit10 2) ∧
      ¬ IsDecimalPermutablePrime (RepunitPrime.repunit10 3) := by
  have hr2 : RepunitPrime.repunit10 2 = 11 := by decide
  have hr3 : RepunitPrime.repunit10 3 = 111 := by decide
  rw [hr2, hr3]
  refine ⟨?_, fun h => by have := h.1; norm_num at this⟩
  have hd : Nat.digits 10 11 = [1, 1] := by norm_num
  unfold IsDecimalPermutablePrime
  rw [hd]
  simp only [List.mem_permutations, ← List.mem_permutations']
  simp [Nat.ofDigits]
  norm_num

/--
Every base-$10$ permutable prime $p > 991$ is a decimal repunit $R_n = (10^n - 1) / 9$.
-/
@[category research open, AMS 11]
theorem permutable_prime_gt_991_is_repunit {p : ℕ} (hp : 991 < p)
    (hperm : IsDecimalPermutablePrime p) :
    ∃ n : ℕ, p = RepunitPrime.repunit10 n := by
  sorry

/--
Infinitely many base-$10$ permutable primes exist.
-/
@[category research open, AMS 11]
theorem infinitely_many_decimal_permutable_primes :
    {p : ℕ | IsDecimalPermutablePrime p}.Infinite := by
  sorry

end PermutablePrime
