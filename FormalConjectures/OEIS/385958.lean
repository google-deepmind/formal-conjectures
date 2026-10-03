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
# Largest prime preserving integrality in reciprocal product recurrence

$a(n)$ is the largest prime $p$ such that $b(n) = b(n-1) \frac{p+1}{p-1}$ is an integer
(A385959), where $b(0) = 1$.

*References:*
- [A385958](https://oeis.org/A385958)
-/
open Nat Finset

namespace OeisA385958

/--
A helper function to find the largest prime $p$ such that $p-1$ divides $2 \cdot k$.
This is the definition of $a(n)$ given $b(n-1)=k$.
Since $k \ge 1$, $2k \ge 2$, and the set of such primes is non-empty (it always contains $p=2$).
-/
noncomputable def largest_prime_divisor_property (k : ℕ) : ℕ :=
  -- Generate candidates p = d + 1 where d is a divisor of 2k. Filter for primes and find the max.
  let candidates := Finset.image (fun d => d + 1) (2 * k).divisors
  let max_prime := candidates.filter Nat.Prime |> Finset.max
  max_prime.getD 0

/--
A385959: The auxiliary sequence $b(n)$.
$b(0) = 1$.
$b(n) = b(n-1) \cdot \frac{a(n)+1}{a(n)-1}$.
-/
noncomputable def b : ℕ → ℕ
| 0 => 1
| n + 1 =>
  let b_prev := b n;
  let p := largest_prime_divisor_property b_prev;
  -- b(n+1) = b_prev + b_prev * 2 / (p - 1)
  b_prev + b_prev * 2 / (p - 1)

/--
The largest prime $p$ such that $b(n) = b(n-1) \frac{p+1}{p-1}$ is an integer.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n > 0 then
    largest_prime_divisor_property (b (n - 1))
  else 0

@[category API, AMS 11]
lemma max_2_3 : (Finset.max ({2, 3} : Finset ℕ)) = some 3 := by
  rw [Finset.max_insert, Finset.max_singleton]
  rfl

@[category API, AMS 11]
lemma max_2_3_5 : (Finset.max ({2, 3, 5} : Finset ℕ)) = some 5 := by
  rw [Finset.max_insert, Finset.max_insert, Finset.max_singleton]
  rfl

@[category API, AMS 11]
lemma max_2_3_7 : (Finset.max ({2, 3, 7} : Finset ℕ)) = some 7 := by
  rw [Finset.max_insert, Finset.max_insert, Finset.max_singleton]
  rfl

@[category API, AMS 11]
lemma max_2_3_5_7_13 : (Finset.max ({2, 3, 5, 7, 13} : Finset ℕ)) = some 13 := by
  rw [Finset.max_insert, Finset.max_insert, Finset.max_insert, Finset.max_insert,
      Finset.max_singleton]
  rfl

@[category API, AMS 11]
lemma prop_1 : largest_prime_divisor_property 1 = 3 := by
  unfold largest_prime_divisor_property
  have h_set :
      (Finset.filter Nat.Prime (Finset.image (fun d => d + 1) (2 * 1).divisors)) = {2, 3} := by
    classical
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Nat.mem_divisors,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨d, hd1, rfl⟩, hp⟩
      have hd_le : d ≤ 2 * 1 := Nat.le_of_dvd (by decide) hd1.1
      have hd_pos : 1 ≤ d := Nat.pos_of_dvd_of_pos hd1.1 (by decide)
      have hdvd := hd1.1
      interval_cases d <;> (revert hdvd hp; decide)
    · rintro (rfl | rfl)
      · refine ⟨⟨1, ⟨by decide, by decide⟩, rfl⟩, Nat.prime_two⟩
      · refine ⟨⟨2, ⟨by decide, by decide⟩, rfl⟩, Nat.prime_three⟩
  change (Option.getD
    (Finset.filter Nat.Prime (Finset.image (fun d => d + 1) (2 * 1).divisors)).max 0) = 3
  rw [h_set, max_2_3]
  rfl

@[category API, AMS 11]
lemma prop_2 : largest_prime_divisor_property 2 = 5 := by
  unfold largest_prime_divisor_property
  have h_set :
      (Finset.filter Nat.Prime (Finset.image (fun d => d + 1) (2 * 2).divisors)) = {2, 3, 5} := by
    classical
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Nat.mem_divisors,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨d, hd1, rfl⟩, hp⟩
      have hd_le : d ≤ 2 * 2 := Nat.le_of_dvd (by decide) hd1.1
      have hd_pos : 1 ≤ d := Nat.pos_of_dvd_of_pos hd1.1 (by decide)
      have hdvd := hd1.1
      interval_cases d <;> (revert hdvd hp; decide)
    · rintro (rfl | rfl | rfl)
      · refine ⟨⟨1, ⟨by decide, by decide⟩, rfl⟩, Nat.prime_two⟩
      · refine ⟨⟨2, ⟨by decide, by decide⟩, rfl⟩, Nat.prime_three⟩
      · refine ⟨⟨4, ⟨by decide, by decide⟩, rfl⟩, Nat.prime_five⟩
  change (Option.getD
    (Finset.filter Nat.Prime (Finset.image (fun d => d + 1) (2 * 2).divisors)).max 0) = 5
  rw [h_set, max_2_3_5]
  rfl

@[category API, AMS 11]
lemma prop_3 : largest_prime_divisor_property 3 = 7 := by
  unfold largest_prime_divisor_property
  have h_set :
      (Finset.filter Nat.Prime (Finset.image (fun d => d + 1) (2 * 3).divisors)) = {2, 3, 7} := by
    classical
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Nat.mem_divisors,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨d, hd1, rfl⟩, hp⟩
      have hd_le : d ≤ 2 * 3 := Nat.le_of_dvd (by decide) hd1.1
      have hd_pos : 1 ≤ d := Nat.pos_of_dvd_of_pos hd1.1 (by decide)
      have hdvd := hd1.1
      interval_cases d <;> (revert hdvd hp; decide)
    · rintro (rfl | rfl | rfl)
      · refine ⟨⟨1, ⟨by decide, by decide⟩, rfl⟩, Nat.prime_two⟩
      · refine ⟨⟨2, ⟨by decide, by decide⟩, rfl⟩, Nat.prime_three⟩
      · refine ⟨⟨6, ⟨by decide, by decide⟩, rfl⟩, Nat.prime_seven⟩
  change (Option.getD
    (Finset.filter Nat.Prime (Finset.image (fun d => d + 1) (2 * 3).divisors)).max 0) = 7
  rw [h_set, max_2_3_7]
  rfl

@[category API, AMS 11]
lemma prop_4 : largest_prime_divisor_property 4 = 5 := by
  unfold largest_prime_divisor_property
  have h_set :
      (Finset.filter Nat.Prime (Finset.image (fun d => d + 1) (2 * 4).divisors)) = {2, 3, 5} := by
    classical
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Nat.mem_divisors,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨d, hd1, rfl⟩, hp⟩
      have hd_le : d ≤ 2 * 4 := Nat.le_of_dvd (by decide) hd1.1
      have hd_pos : 1 ≤ d := Nat.pos_of_dvd_of_pos hd1.1 (by decide)
      have hdvd := hd1.1
      interval_cases d <;> (revert hdvd hp; decide)
    · rintro (rfl | rfl | rfl)
      · refine ⟨⟨1, ⟨by decide, by decide⟩, rfl⟩, Nat.prime_two⟩
      · refine ⟨⟨2, ⟨by decide, by decide⟩, rfl⟩, Nat.prime_three⟩
      · refine ⟨⟨4, ⟨by decide, by decide⟩, rfl⟩, Nat.prime_five⟩
  change (Option.getD
    (Finset.filter Nat.Prime (Finset.image (fun d => d + 1) (2 * 4).divisors)).max 0) = 5
  rw [h_set, max_2_3_5]
  rfl

@[category API, AMS 11]
lemma prop_6 : largest_prime_divisor_property 6 = 13 := by
  unfold largest_prime_divisor_property
  have h_set :
      (Finset.filter Nat.Prime (Finset.image (fun d => d + 1) (2 * 6).divisors)) =
        {2, 3, 5, 7, 13} := by
    classical
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Nat.mem_divisors,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨d, hd1, rfl⟩, hp⟩
      have hd_le : d ≤ 2 * 6 := Nat.le_of_dvd (by decide) hd1.1
      have hd_pos : 1 ≤ d := Nat.pos_of_dvd_of_pos hd1.1 (by decide)
      have hdvd := hd1.1
      interval_cases d <;> (revert hdvd hp; decide)
    · rintro (rfl | rfl | rfl | rfl | rfl)
      · refine ⟨⟨1, ⟨by decide, by decide⟩, rfl⟩, Nat.prime_two⟩
      · refine ⟨⟨2, ⟨by decide, by decide⟩, rfl⟩, Nat.prime_three⟩
      · refine ⟨⟨4, ⟨by decide, by decide⟩, rfl⟩, Nat.prime_five⟩
      · refine ⟨⟨6, ⟨by decide, by decide⟩, rfl⟩, Nat.prime_seven⟩
      · refine ⟨⟨12, ⟨by decide, by decide⟩, rfl⟩, by norm_num⟩
  change (Option.getD
    (Finset.filter Nat.Prime (Finset.image (fun d => d + 1) (2 * 6).divisors)).max 0) = 13
  rw [h_set, max_2_3_5_7_13]
  rfl

@[category API, AMS 11]
lemma b_0 : b 0 = 1 := rfl
@[category API, AMS 11]
lemma b_1 : b 1 = 2 := by show 1 + 1 * 2 / (largest_prime_divisor_property 1 - 1) = 2; rw [prop_1]
@[category API, AMS 11]
lemma b_2 : b 2 = 3 := by show 2 + 2 * 2 / (largest_prime_divisor_property 2 - 1) = 3; rw [prop_2]
@[category API, AMS 11]
lemma b_3 : b 3 = 4 := by show 3 + 3 * 2 / (largest_prime_divisor_property 3 - 1) = 4; rw [prop_3]
@[category API, AMS 11]
lemma b_4 : b 4 = 6 := by show 4 + 4 * 2 / (largest_prime_divisor_property 4 - 1) = 6; rw [prop_4]

@[category test, AMS 11]
theorem a_1 : a 1 = 3 := by unfold a; rw [b_0, prop_1]; rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 5 := by unfold a; rw [b_1, prop_2]; rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 7 := by unfold a; rw [b_2, prop_3]; rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 5 := by unfold a; rw [b_3, prop_4]; rfl

@[category test, AMS 11]
theorem a_5 : a 5 = 13 := by unfold a; rw [b_4, prop_6]; rfl

/--
Conjecture: Does this sequence contain all odd primes?
Formalization: For every odd prime $p$, there exists $n \in \mathbb{N}^+$ such that $a(n) = p$.
-/
@[category research open, AMS 11]
theorem odd_primes_appear :
    answer(sorry) ↔ ∀ (p : ℕ), p.Prime → p ≠ 2 → ∃ (n : ℕ+), a n = p := by
  sorry

end OeisA385958
