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
# Representations of $12n-1$ as pairwise products of three odd primes

$a(n)$ is the number of representations of $12n-1$ in the form $pq + pr + qr$ with odd primes
$p \le q \le r$.

*References:*
- [A369462](https://oeis.org/A369462)
-/
open Nat Finset

set_option maxRecDepth 1000000
namespace OeisA369462

/--
Number of representations of $12n-1$ as $pq + pr + qr$ with odd primes $p \le q \le r$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if 1 ≤ n then
    let N : ℕ := 12 * n - 1
    -- N is the target number. Since p*q < N, p, q, r are all bounded by N.
    let B := N
    let search_range := range (B + 1)
    let search_space := search_range.product (search_range.product search_range)

    (search_space.filter (fun t : ℕ × ℕ × ℕ =>
      let p := t.fst
      let q := t.snd.fst
      let r := t.snd.snd
      -- 1. All must be odd primes (Prime and not equal to 2)
      p.Prime ∧ p ≠ 2 ∧ q.Prime ∧ q ≠ 2 ∧ r.Prime ∧ r ≠ 2 ∧
      -- 2. Order and sum constraint.
      p ≤ q ∧ q ≤ r ∧ p * q + p * r + q * r = N
    )).card
  else
    0

@[category API, AMS 11]
lemma a_eq_0_of_N_le_50 {n : ℕ} (hn1 : 1 ≤ n) (hn2 : 12 * n - 1 ≤ 50) : a n = 0 := by
  unfold a
  rw [if_pos hn1]
  dsimp
  have h_empty : (Finset.filter (fun t : ℕ × ℕ × ℕ =>
      t.1.Prime ∧ t.1 ≠ 2 ∧ t.2.1.Prime ∧ t.2.1 ≠ 2 ∧ t.2.2.Prime ∧ t.2.2 ≠ 2 ∧
      t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧ t.1 * t.2.1 + t.1 * t.2.2 + t.2.1 * t.2.2 = 12 * n - 1)
    ((range (12 * n - 1 + 1)) ×ˢ
     ((range (12 * n - 1 + 1)) ×ˢ (range (12 * n - 1 + 1))))) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    rintro ⟨p, q, r⟩ _
    simp only [not_and]
    intro hp hp2 hq hq2 hr hr2 hpq hqr
    have hp3 : 3 ≤ p := by
      cases p with
      | zero => exact False.elim (Nat.not_prime_zero hp)
      | succ p' =>
        cases p' with
        | zero => exact False.elim (Nat.not_prime_one hp)
        | succ p'' =>
          cases p'' with
          | zero => exact False.elim (hp2 rfl)
          | succ p''' => omega
    have hq3 : 3 ≤ q := by omega
    have hr3 : 3 ≤ r := by omega
    have hN : 12 * n - 1 ≤ 47 := by omega
    intro heq
    have : p * q + p * r + q * r ≤ 47 := heq.symm ▸ hN
    have hr7 : r < 7 := by
      by_contra!
      nlinarith
    have h_r : r = 3 ∨ r = 5 := by
      have : r ≤ 6 := by omega
      interval_cases r
      · left; rfl
      · exact False.elim (by revert hr; decide)
      · right; rfl
      · exact False.elim (by revert hr; decide)
    have h_q : q = 3 ∨ q = 5 := by
      have : q ≤ 5 := by omega
      interval_cases q
      · left; rfl
      · exact False.elim (by revert hq; decide)
      · right; rfl
    have h_p : p = 3 ∨ p = 5 := by
      have : p ≤ 5 := by omega
      interval_cases p
      · left; rfl
      · exact False.elim (by revert hp; decide)
      · right; rfl
    rcases h_p with rfl | rfl
    · rcases h_q with rfl | rfl
      · rcases h_r with rfl | rfl
        · revert heq; norm_num; intro heq; omega
        · revert heq; norm_num; intro heq; omega
      · rcases h_r with rfl | rfl
        · revert hqr; norm_num
        · revert heq; norm_num; intro heq; omega
    · rcases h_q with rfl | rfl
      · rcases h_r with rfl | rfl
        · revert hpq; norm_num
        · revert hpq; norm_num
      · rcases h_r with rfl | rfl
        · revert hqr; norm_num
        · revert heq; norm_num; intro heq; omega
  have h_eq : Finset.filter (fun t =>
        t.1.Prime ∧
          ¬t.1 = 2 ∧
            t.2.1.Prime ∧
              ¬t.2.1 = 2 ∧
                t.2.2.Prime ∧
                  ¬t.2.2 = 2 ∧ t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧
                  t.1 * t.2.1 + t.1 * t.2.2 + t.2.1 * t.2.2 = 12 * n - 1)
      (range (12 * n - 1 + 1) ×ˢ
       range (12 * n - 1 + 1) ×ˢ range (12 * n - 1 + 1)) = ∅ := h_empty
  rw [h_eq]
  exact rfl

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := a_eq_0_of_N_le_50 (by norm_num) (by norm_num)

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := a_eq_0_of_N_le_50 (by norm_num) (by norm_num)

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := a_eq_0_of_N_le_50 (by norm_num) (by norm_num)

@[category test, AMS 11]
theorem a_4 : a 4 = 0 := a_eq_0_of_N_le_50 (by norm_num) (by norm_num)

/--
Conjecture a: Is there only a finite number of 0's in this sequence?
-/
@[category research open, AMS 11]
theorem finitely_many_zeros : answer(sorry) ↔ {n : ℕ | a n = 0}.Finite := by
  sorry

end OeisA369462
