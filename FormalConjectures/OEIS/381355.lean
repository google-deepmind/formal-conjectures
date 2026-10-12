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
# A logarithmic derivative with prime-divisible coefficients

Let $F(x)$ be the generating function of A381353, with $F(0)=1$, $[x]F(x)=1$, and
$[x^n]F(x)^{p_n}=0$ for $n>1$, where $p_n$ is the $n$-th prime.
The sequence is defined by $\sum_{n\ge1}a(n)x^n=xF'(x)/F(x)$.

*References:*
- [A381355](https://oeis.org/A381355)
- [A381353](https://oeis.org/A381353)
- [Li26] Wentao Li, [Prime divisibility of logarithmic-derivative coefficients](https://github.com/VictorLiwentao/lean-oeis-proofs/blob/0a23974e54b90afd1453ef02c27cf8f617bad940/proofs/new-proofs/A381355/PROOF.md), 2026.
-/

@[expose] public section

namespace OeisA381355

open PowerSeries

/-- The $n$-th prime, indexed from $p_1=2$. -/
noncomputable def primeN (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- The coefficients of $F$, obtained successively from $[x^n]F(x)^{p_n}=0$. -/
noncomputable def f : ℕ → ℤ :=
  Nat.strongRec fun n ih =>
    if n = 0 then 1
    else if n = 1 then 1
    else
      -(coeff n
          (PowerSeries.mk (fun k => if h : k < n then ih k h else 0) ^ primeN n) /
        (primeN n : ℤ))

/-- The generating function of A381353. -/
noncomputable def series : PowerSeries ℤ := PowerSeries.mk f

/-- The coefficients of $xF'(x)/F(x)$. -/
noncomputable def a (n : ℕ) : ℤ :=
  coeff n (X * derivative ℤ series * invOfUnit series 1)

@[category API, AMS 11]
private lemma f_eq (n : ℕ) :
    f n = if n = 0 then 1 else if n = 1 then 1 else
      -(coeff n (PowerSeries.mk (fun k => if k < n then f k else 0) ^ primeN n) /
        (primeN n : ℤ)) := by
  rw [f, Nat.strongRec_eq]
  rfl

@[category API, AMS 11]
private lemma f_0 : f 0 = 1 := by rw [f_eq]; norm_num
@[category API, AMS 11]
private lemma f_1 : f 1 = 1 := by rw [f_eq]; norm_num

@[category API, AMS 11]
private lemma coeff_mul_range (n : ℕ) (F G : PowerSeries ℤ) :
    coeff n (F * G) = ∑ k ∈ Finset.range (n + 1), coeff k F * coeff (n - k) G := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

@[category API, AMS 11]
private lemma coeff_pow_succ (n p : ℕ) (G : PowerSeries ℤ) :
    coeff n (G ^ (p + 1)) =
      ∑ k ∈ Finset.range (n + 1), coeff k (G ^ p) * coeff (n - k) G := by
  rw [pow_succ, coeff_mul_range]

@[category API, AMS 11]
private lemma f_2 : f 2 = -1 := by
  rw [f_eq]
  norm_num [primeN, Nat.nth_prime_one_eq_three, coeff_pow_succ,
    Finset.sum_range_succ, coeff_mk, coeff_one, f_0, f_1]

@[category API, AMS 11]
private lemma f_3 : f 3 = 2 := by
  rw [f_eq]
  norm_num [primeN, Nat.nth_prime_two_eq_five, coeff_pow_succ,
    Finset.sum_range_succ, coeff_mk, coeff_one, f_0, f_1, f_2]

@[category API, AMS 11]
private lemma coeff_natCast (n k : ℕ) :
    coeff n (k : PowerSeries ℤ) = if n = 0 then (k : ℤ) else 0 := by
  have h : (k : PowerSeries ℤ) = C (k : ℤ) := by simp
  rw [h, coeff_C]

@[category API, AMS 11]
private lemma coeff_natCast_mul (n k : ℕ) (G : PowerSeries ℤ) :
    coeff n ((k : PowerSeries ℤ) * G) = (k : ℤ) * coeff n G := by
  have h : (k : PowerSeries ℤ) = C (k : ℤ) := by simp
  rw [h, coeff_C_mul]

@[category API, AMS 11]
private lemma coeff_ofNat (n k : ℕ) [k.AtLeastTwo] :
    coeff n (ofNat(k) : PowerSeries ℤ) = if n = 0 then (ofNat(k) : ℤ) else 0 := by
  exact coeff_natCast n k

@[category API, AMS 11]
private lemma coeff_ofNat_mul (n k : ℕ) [k.AtLeastTwo] (G : PowerSeries ℤ) :
    coeff n ((ofNat(k) : PowerSeries ℤ) * G) = (ofNat(k) : ℤ) * coeff n G := by
  exact coeff_natCast_mul n k G

@[category API, AMS 11]
private lemma f_4 : f 4 = -5 := by
  have ht : PowerSeries.mk (fun k => if k < 4 then f k else 0) =
      (1 + X - X ^ 2 + 2 * X ^ 3 : PowerSeries ℤ) := by
    ext n
    by_cases hn : n < 4
    · interval_cases n <;>
        norm_num [coeff_mk, f_0, f_1, f_2, f_3, coeff_X_pow, coeff_X, coeff_ofNat_mul]
    · have h0 : n ≠ 0 := by omega
      have h1 : n ≠ 1 := by omega
      have h2 : n ≠ 2 := by omega
      have h3 : n ≠ 3 := by omega
      simp [coeff_mk, hn, coeff_X_pow, h0, h1, h2, h3, coeff_X, coeff_ofNat_mul]
  rw [f_eq]
  norm_num only [primeN, Nat.reduceSub, Nat.nth_prime_three_eq_seven, Nat.cast_ofNat,
    show (4 : ℕ) ≠ 0 from by decide, show (4 : ℕ) ≠ 1 from by decide, if_false]
  rw [ht]
  ring_nf
  norm_num [map_add, coeff_mul, coeff_X_pow, coeff_X, coeff_ofNat, map_ofNat,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]

@[category API, AMS 11]
private lemma f_5 : f 5 = 13 := by
  have ht : PowerSeries.mk (fun k => if k < 5 then f k else 0) =
      (1 + X - X ^ 2 + 2 * X ^ 3 - 5 * X ^ 4 : PowerSeries ℤ) := by
    ext n
    by_cases hn : n < 5
    · interval_cases n <;>
        norm_num [coeff_mk, f_0, f_1, f_2, f_3, f_4, coeff_X_pow, coeff_X, coeff_ofNat_mul]
    · have h0 : n ≠ 0 := by omega
      have h1 : n ≠ 1 := by omega
      have h2 : n ≠ 2 := by omega
      have h3 : n ≠ 3 := by omega
      have h4 : n ≠ 4 := by omega
      simp [coeff_mk, hn, coeff_X_pow, h0, h1, h2, h3, h4, coeff_X, coeff_ofNat_mul]
  rw [f_eq]
  norm_num only [primeN, Nat.reduceSub, Nat.nth_prime_four_eq_eleven, Nat.cast_ofNat,
    show (5 : ℕ) ≠ 0 from by decide, show (5 : ℕ) ≠ 1 from by decide, if_false]
  rw [ht]
  ring_nf
  norm_num [map_add, coeff_mul, coeff_X_pow, coeff_X, coeff_ofNat, map_ofNat,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]

@[category API, AMS 11]
private lemma inv_coeff (n : ℕ) :
    coeff n (invOfUnit series 1) = if n = 0 then 1 else
      -∑ k ∈ Finset.range (n + 1),
        if n - k < n then f k * coeff (n - k) (invOfUnit series 1) else 0 := by
  rw [coeff_invOfUnit]
  simp only [inv_one, Units.val_one, neg_one_mul, series, coeff_mk,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

@[category API, AMS 11]
private lemma inv_0 : coeff 0 (invOfUnit series 1) = 1 := by
  rw [inv_coeff]
  norm_num [Finset.sum_range_succ, f_0]

@[category API, AMS 11]
private lemma inv_1 : coeff 1 (invOfUnit series 1) = -1 := by
  rw [inv_coeff]
  norm_num [Finset.sum_range_succ, f_0, f_1, inv_0]

@[category API, AMS 11]
private lemma inv_2 : coeff 2 (invOfUnit series 1) = 2 := by
  rw [inv_coeff]
  norm_num [Finset.sum_range_succ, f_0, f_1, f_2, inv_0, inv_1]

@[category API, AMS 11]
private lemma inv_3 : coeff 3 (invOfUnit series 1) = -5 := by
  rw [inv_coeff]
  norm_num [Finset.sum_range_succ, f_0, f_1, f_2, f_3, inv_0, inv_1, inv_2]

@[category API, AMS 11]
private lemma inv_4 : coeff 4 (invOfUnit series 1) = 14 := by
  rw [inv_coeff]
  norm_num [Finset.sum_range_succ, f_0, f_1, f_2, f_3, f_4, inv_0, inv_1, inv_2, inv_3]

@[category API, AMS 11]
private lemma a_succ (n : ℕ) :
    a (n + 1) = ∑ k ∈ Finset.range (n + 1),
      (f (k + 1) * (k + 1)) * coeff (n - k) (invOfUnit series 1) := by
  rw [a, mul_assoc, coeff_succ_X_mul, coeff_mul_range]
  simp only [coeff_derivative, series, coeff_mk]

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  rw [show 1 = 0 + 1 from rfl, a_succ]
  norm_num [Finset.sum_range_succ, inv_0, inv_1, inv_2, inv_3, inv_4, f_0, f_1]

@[category test, AMS 11]
theorem a_2 : a 2 = -3 := by
  rw [show 2 = 1 + 1 from rfl, a_succ]
  norm_num [Finset.sum_range_succ, inv_0, inv_1, inv_2, inv_3, inv_4, f_0, f_1, f_2]

@[category test, AMS 11]
theorem a_3 : a 3 = 10 := by
  rw [show 3 = 2 + 1 from rfl, a_succ]
  norm_num [Finset.sum_range_succ, inv_0, inv_1, inv_2, inv_3, inv_4, f_0, f_1, f_2, f_3]

@[category test, AMS 11]
theorem a_4 : a 4 = -35 := by
  rw [show 4 = 3 + 1 from rfl, a_succ]
  norm_num [Finset.sum_range_succ, inv_0, inv_1, inv_2, inv_3, inv_4, f_0, f_1, f_2, f_3, f_4]

@[category test, AMS 11]
theorem a_5 : a 5 = 121 := by
  rw [show 5 = 4 + 1 from rfl, a_succ]
  norm_num [Finset.sum_range_succ, inv_0, inv_1, inv_2, inv_3, inv_4, f_0, f_1, f_2, f_3, f_4, f_5]

/--
"Conjecture: $a(n)$ is divisible by $\operatorname{prime}(n)$ for $n > 1$."
- Paul D. Hanna, Mar 11 2025.

Proved and formalized in Lean by Wentao Li, with AI assistance; see [Li26].
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/VictorLiwentao/lean-oeis-proofs/blob/0a23974e54b90afd1453ef02c27cf8f617bad940/LeanOeisProofs/NewProofs/A381355.lean#L380"]
theorem conjecture (n : ℕ) (hn : 1 < n) : (primeN n : ℤ) ∣ a n := by
  sorry

end OeisA381355
