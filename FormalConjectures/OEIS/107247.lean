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
# Sum of squares of nonacci numbers

Sum of squares of nonacci numbers (Fibonacci 9-step numbers).

*References:*
- [A107247](https://oeis.org/A107247)
-/

@[expose] public section

namespace OeisA107247

/-- Nonacci number (Fibonacci 9-step number).
$F_9(n)$ is defined by the linear recurrence $F_9(n+9) = \sum_{i=0}^8 F_9(n+i)$,
with $F_9(0) = \dots = F_9(7) = 0$ and $F_9(8) = 1$. -/
def nonacci : ℕ → ℕ
  | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 0 | 6 => 0 | 7 => 0
  | 8 => 1
  | n + 9 =>
    nonacci (n + 8) + nonacci (n + 7) + nonacci (n + 6) + nonacci (n + 5) +
    nonacci (n + 4) + nonacci (n + 3) + nonacci (n + 2) + nonacci (n + 1) + nonacci n

/--
The primary defining sequence `a`.
`a n` is the sum of squares of nonacci numbers (Fibonacci 9-step numbers).
The official sequence matches the sum up to `n + 1` of the standard nonacci numbers
to align with the offset.
-/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 2), (nonacci k) ^ 2

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by decide

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 0 := by decide

/-- Trial division by all odd numbers up to the square root, checked by the kernel. (The proof
term that `norm_num` builds for a prime of this size is too deep for the kernel.) -/
@[category API, AMS 11]
private lemma prime_5045088967 : Nat.Prime 5045088967 := by
  have hall : (List.range' 3 35514 2).all (fun m => 5045088967 % m != 0) = true := by
    decide +kernel
  rw [Nat.prime_def_le_sqrt]
  refine ⟨by norm_num, fun m hm2 hms hdvd => ?_⟩
  have hsq : Nat.sqrt 5045088967 = 71028 := by norm_num
  rw [hsq] at hms
  rcases Nat.even_or_odd m with he | ho
  · have h2 : 2 ∣ 5045088967 := (even_iff_two_dvd.mp he).trans hdvd
    omega
  · have hmem : m ∈ List.range' 3 35514 2 := by
      obtain ⟨j, rfl⟩ := ho
      exact List.mem_range'.mpr ⟨j - 1, by omega, by omega⟩
    have h := List.all_eq_true.mp hall m hmem
    simp [Nat.dvd_iff_mod_eq_zero.mp hdvd] at h

/--
Primes in this sequence include: $a(8) = 2$.
Semiprimes in this sequence include: $a(9) = 6 = 2 * 3$, $a(10) = 22 = 2 * 11$,
$a(11) = 86 = 2 * 43$, $a(13) = 1366 = 2 * 683$, $a(14) = 5462 = 2 * 2731$,
$a(16) = 87382 = 2 * 43691$, $a(17) = 348503 = 37 * 9419$,
$a(27) = 358201316657 = 71 * 5045088967$.
(Note: The OEIS comment uses 1-based indexing, so their indices are shifted by +1 compared
to this formalization).
-/
@[category textbook, AMS 11]
theorem known_prime_and_semiprimes :
  (a 8).Prime ∧
  (a 9).IsSemiprime ∧
  (a 10).IsSemiprime ∧
  (a 11).IsSemiprime ∧
  (a 13).IsSemiprime ∧
  (a 14).IsSemiprime ∧
  (a 16).IsSemiprime ∧
  (a 17).IsSemiprime ∧
  (a 27).IsSemiprime := by
  have h8 : a 8 = 2 := by decide +kernel
  have h9 : a 9 = 2 * 3 := by decide +kernel
  have h10 : a 10 = 2 * 11 := by decide +kernel
  have h11 : a 11 = 2 * 43 := by decide +kernel
  have h13 : a 13 = 2 * 683 := by decide +kernel
  have h14 : a 14 = 2 * 2731 := by decide +kernel
  have h16 : a 16 = 2 * 43691 := by decide +kernel
  have h17 : a 17 = 37 * 9419 := by decide +kernel
  have h27 : a 27 = 71 * 5045088967 := by decide +kernel
  rw [h8, h9, h10, h11, h13, h14, h16, h17, h27]
  exact ⟨by norm_num,
    Nat.Prime.mul_isAlmostPrime_two (by norm_num) (by norm_num),
    Nat.Prime.mul_isAlmostPrime_two (by norm_num) (by norm_num),
    Nat.Prime.mul_isAlmostPrime_two (by norm_num) (by norm_num),
    Nat.Prime.mul_isAlmostPrime_two (by norm_num) (by norm_num),
    Nat.Prime.mul_isAlmostPrime_two (by norm_num) (by norm_num),
    Nat.Prime.mul_isAlmostPrime_two (by norm_num) (by norm_num),
    Nat.Prime.mul_isAlmostPrime_two (by norm_num) (by norm_num),
    Nat.Prime.mul_isAlmostPrime_two (by norm_num) prime_5045088967⟩

def conjecture.answer : ℕ := sorry

/--
Primes in this sequence include: $a(8) = 2$, which is next?
-/
@[category research open, question value, AMS 11]
theorem conjecture :
    conjecture.answer = a (sInf {n : ℕ | 8 < n ∧ (a n).Prime}) := by
  sorry

end OeisA107247
