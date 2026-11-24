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
# Numbers $n$ such that the perfect deficiency of $n$ is $\le 10$.

The perfect deficiency of $n$ (A109883) is the remainder after greedily subtracting
from $n$ its divisors in increasing order, skipping any divisor larger than the
current remainder.

*References:*
- [A108864](https://oeis.org/A108864)
- [A109883](https://oeis.org/A109883)
-/

@[expose] public section

namespace OeisA108864

open Nat Finset Int

/--
The perfect deficiency of $n$ (A109883): the remainder after greedily subtracting
from $n$ its divisors in increasing order, skipping any divisor larger than the
current remainder.
-/
def perfectDeficiency (n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl (fun m d => if d ∣ n ∧ d ≤ m then m - d else m) n

/--
The condition for a number $n$ to be in the sequence.
It satisfies $0 < n$ and its perfect deficiency is $\le 10$.
-/
def A (n : ℕ) : Prop :=
  0 < n ∧ perfectDeficiency n ≤ 10

instance : DecidablePred A := by
  unfold A
  infer_instance

/--
The primary defining sequence `a`.
$a(n)$ is the $n$-th number (0-indexed) such that its perfect deficiency is $\le 10$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  n.nth A

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by
  have h1 : A 1 := by decide
  have hcnt : Nat.count A 1 = 0 := by decide
  have := Nat.nth_count (p := A) h1
  rwa [hcnt] at this

@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by
  have h2 : A 2 := by decide
  have hcnt : Nat.count A 2 = 1 := by decide
  have := Nat.nth_count (p := A) h2
  rwa [hcnt] at this

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by
  have h3 : A 3 := by decide
  have hcnt : Nat.count A 3 = 2 := by decide
  have := Nat.nth_count (p := A) h3
  rwa [hcnt] at this

@[category test, AMS 11]
theorem a_3 : a 3 = 4 := by
  have h4 : A 4 := by decide
  have hcnt : Nat.count A 4 = 3 := by decide
  have := Nat.nth_count (p := A) h4
  rwa [hcnt] at this

@[category test, AMS 11]
theorem a_4 : a 4 = 5 := by
  have h5 : A 5 := by decide
  have hcnt : Nat.count A 5 = 4 := by decide
  have := Nat.nth_count (p := A) h5
  rwa [hcnt] at this

@[category API, AMS 11]
private lemma foldl_range_eq_sub_sum (n k : ℕ)
    (hsum : ∑ d ∈ (Finset.range k).filter (· ∣ n), d ≤ n) :
    (List.range k).foldl (fun m d ↦ if d ∣ n ∧ d ≤ m then m - d else m) n =
      n - ∑ d ∈ (Finset.range k).filter (· ∣ n), d := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [Finset.range_add_one] at hsum ⊢
    by_cases hk : k ∣ n
    · rw [Finset.filter_insert, if_pos hk, Finset.sum_insert (by simp)] at hsum ⊢
      rw [ih (by omega)]
      have hle : k ≤ n - ∑ d ∈ (Finset.range k).filter (· ∣ n), d := by omega
      simp only [hk, hle, and_self, ↓reduceIte]
      omega
    · rw [Finset.filter_insert, if_neg hk] at hsum ⊢
      simp [ih hsum, hk]

/-- For any $n > 1$ whose proper divisors sum to at most $n$ (equivalently $\sigma_1(n) \le 2n$),
greedy divisor subtraction subtracts every proper divisor and skips $n$, giving
$\operatorname{perfectDeficiency}(n) = 2n - \sigma_1(n)$. -/
@[category API, AMS 11]
lemma perfectDeficiency_of_sum_divisors_le {n : ℕ} (hn : 1 < n)
    (hdef : ∑ d ∈ n.divisors, d ≤ 2 * n) :
    perfectDeficiency n = 2 * n - ∑ d ∈ n.divisors, d := by
  unfold perfectDeficiency
  have hfilt : (Finset.range n).filter (· ∣ n) = n.properDivisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_properDivisors, and_comm]
  have hdiv : ∑ d ∈ n.divisors, d = ∑ d ∈ n.properDivisors, d + n := by
    rw [← Nat.cons_self_properDivisors (by omega), Finset.sum_cons]
    omega
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
    foldl_range_eq_sub_sum n n (by rw [hfilt]; omega)]
  have hpos : 1 ≤ ∑ d ∈ (Finset.range n).filter (· ∣ n), d :=
    Finset.single_le_sum (f := id) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn, one_dvd n⟩)
  have hnot_le : ¬ n ≤ n - ∑ d ∈ (Finset.range n).filter (· ∣ n), d := by omega
  simp only [dvd_refl, hnot_le, and_false, ↓reduceIte]
  rw [hfilt]
  omega

/-- The $59$ terms of A108864 up to $1155$. -/
private def first59Terms : Finset ℕ :=
  {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 21, 22, 24,
   26, 28, 30, 32, 40, 42, 44, 50, 52, 60, 64, 68, 72, 110, 120, 126, 128,
   130, 136, 144, 150, 152, 180, 184, 204, 228, 256, 315, 462, 496, 512,
   528, 592, 656, 750, 884, 1012, 1024, 1155}

/--
Is $1155$ the last odd number in this sequence?
($1155$ is the $59$th term starting from $1$, corresponding to $a(58) = 1155$).

The answer is **no**: an odd term exceeding $1155$ is
$815634435 = 1155 \cdot 547 \cdot 1291 = 3 \cdot 5 \cdot 7 \cdot 11 \cdot 547 \cdot 1291$.
For primes $11 < p < q$, $2(1155pq) - \sigma_1(1155pq) = 6\bigl((p - 384)(q - 384) - 147840\bigr)$,
and $(p - 384)(q - 384) = 147841 = 163 \cdot 907$ gives $(p, q) = (547, 1291)$ with
$\sigma_1(815634435) = 2 \cdot 815634435 - 6$, hence perfect deficiency $6 \le 10$.
-/
@[category research solved, question, AMS 11]
theorem conjecture :
    ¬ ∀ n > 58, Even (a n) := by
  have hp547 : (547 : ℕ).Prime := by norm_num
  have hp1291 : (1291 : ℕ).Prime := by norm_num
  have hsum1155 : ∑ d ∈ (1155 : ℕ).divisors, d = 2304 := by decide +kernel
  have hsum1 : ∑ d ∈ (631785 : ℕ).divisors, d = 1262592 := by
    rw [show (631785 : ℕ) = 1155 * 547 by norm_num,
      Nat.Coprime.sum_divisors_mul (by decide), Nat.Prime.divisors hp547,
      Finset.sum_pair (by decide), hsum1155]
    norm_num
  have hsum2 : ∑ d ∈ (815634435 : ℕ).divisors, d = 1631268864 := by
    rw [show (815634435 : ℕ) = 631785 * 1291 by norm_num,
      Nat.Coprime.sum_divisors_mul (by decide), Nat.Prime.divisors hp1291,
      Finset.sum_pair (by decide), hsum1]
    norm_num
  have hpd : perfectDeficiency 815634435 = 6 := by
    rw [perfectDeficiency_of_sum_divisors_le (by norm_num) (by omega), hsum2]
  have hA : A 815634435 := ⟨by norm_num, by omega⟩
  have hcard : first59Terms.card = 59 := by decide +kernel
  have hearlier : ∀ m ∈ first59Terms, m < 815634435 ∧ A m := by decide +kernel
  have hcount : 59 ≤ Nat.count A 815634435 := by
    rw [Nat.count_eq_card_filter_range, ← hcard]
    exact Finset.card_le_card fun m hm ↦
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hearlier m hm).1, (hearlier m hm).2⟩
  intro h
  obtain ⟨k, hk⟩ := h (Nat.count A 815634435) (by omega)
  rw [a, Nat.nth_count hA] at hk
  omega

end OeisA108864
