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
import FormalConjectures.Util.ProblemImports
import Mathlib.NumberTheory.LucasPrimality

/-!
$a(n)$ is the minimum integer $k$ such that the smallest prime factor of the
$n$-th Fermat number exceeds $2^(2^n - k)$.

*References:*
- [A358684](https://oeis.org/A358684)
- [SA22](https://doi.org/10.26493/2590-9770.1473.ec5) Lorenzo Sauras-Altuzarra, *Some properties of the factors of Fermat numbers*, Art Discrete Appl. Math. (2022).
-/


namespace OeisA358684

open Nat

/--
A358684: $a(n)$ is the minimum integer $k$ such that the smallest prime factor of the $n$-th Fermat
number exceeds $2^{2^n - k}$.
Let $F_n = 2^{2^n} + 1$ be the $n$-th Fermat number, and $P_n$ be its smallest prime factor.
The definition of $a(n)$ is equivalent to the closed form:
$$a(n) = 2^n - \lfloor \log_2(P_n) \rfloor$$
where $P_n = \operatorname{minFac}(\operatorname{fermatNumber} n)$.
The subtraction is defined in $\mathbb{N}$ and is safe
 since $P_n \le F_n$, implying $\log_2 P_n < 2^n$.
-/
def a (n : ℕ) : ℕ :=
  letI pn := minFac (fermatNumber n)
  (2 ^ n) - (log2 pn)

/--
The "original" definition: $a'(n)$ is the minimum $k$ such that $P_n > 2^{2^n - k}$.
We use `Nat.find` which returns the smallest natural number satisfying a predicate.
-/
noncomputable def a' (n : ℕ) : ℕ :=
  letI Pn := minFac (fermatNumber n)
  Nat.find (show ∃ k, Pn > 2 ^ (2 ^ n - k) from by
    use 2^n
    simp only [tsub_self, pow_zero]
    simp [Pn]
    unfold Nat.fermatNumber
    exact (Nat.minFac_prime (by norm_num)).one_lt
  )


/--
The log2 of the smallest prime factor of $F_n$ is at most $2^n$.
-/
@[category undergraduate, AMS 11]
private lemma log2_minFac_le (n : ℕ) : log2 (fermatNumber n).minFac ≤ 2^n := by
  rw [log2_eq_log_two]
  refine (log_mono_right (minFac_le (by rw [fermatNumber]; norm_num))).trans_eq ?_
  rw [fermatNumber, log_eq_of_pow_le_of_lt_pow (le_add_right _ _)]
  rw [pow_succ, mul_two]
  gcongr
  exact one_lt_pow (by norm_num) (by norm_num)

/--
The minimization definition is equivalent to the closed form.
-/
@[category API, AMS 11]
theorem a_equiv_a' (n : ℕ) : a n = a' n := by
  unfold a a'; set Pn := (fermatNumber n).minFac
  rw [Eq.comm, Nat.find_eq_iff]
  constructor
  · rw [tsub_tsub_cancel_of_le (log2_minFac_le n), log2_eq_log_two]
    refine lt_of_le_of_ne (pow_log_le_self 2 (Nat.Prime.ne_zero (minFac_prime ?_))) fun h => ?_
    · rw [fermatNumber]
      norm_num
    · have hPn : Pn.Prime := minFac_prime (by rw [fermatNumber]; norm_num)
      have hnz := log2_eq_log_two ▸ (Nat.log_pos one_lt_two hPn.two_le).ne'
      refine (Nat.not_even_iff_odd.mpr <| (odd_pow_iff hnz).mp ?_) even_two
      rw [log2_eq_log_two, h]
      exact Odd.of_dvd_nat (odd_fermatNumber n) (minFac_dvd _)
  · intro m hm; simp only [not_lt]
    rw [lt_tsub_iff_left] at hm
    rw [log2_eq_log_two] at hm
    refine (lt_pow_succ_log_self (b:=2) (by norm_num) _).le.trans ?_
    apply Nat.pow_le_pow_right (by norm_num)
    apply le_tsub_of_add_le_right
    have := succ_le_of_lt hm
    omega

@[category test, AMS 11]
theorem zero : a 0 = 0 := by norm_num [a]; simp [log2_def]

@[category test, AMS 11]
theorem one : a 1 = 0 := by norm_num [a]; simp [log2_def]

@[category test, AMS 11]
theorem two : a 2 = 0 := by norm_num [a]; simp [log2_def]

@[category test, AMS 11]
theorem three : a 3 = 0 := by
  norm_num only [a, Nat.log2_eq_log_two,Nat.fermatNumber]

@[category test, AMS 11]
theorem four : a 0 = 0 := by norm_num [a]; simp [log2_def]

@[category test, AMS 11]
theorem five : a 5 = 23 := by
  norm_num [a, fermatNumber,Nat.log2_eq_log_two]



-- Verified fast exponentiation for Pratt certificates
@[category API]
def modPowAux (m : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, res => res
  | fuel + 1, b, e, res =>
    if e = 0 then res
    else if e % 2 = 1 then
      modPowAux m fuel ((b * b) % m) (e / 2) ((res * b) % m)
    else
      modPowAux m fuel ((b * b) % m) (e / 2) res

@[category API]
lemma modPowAux_spec (m fuel b e res : ℕ) (h_fuel : e < 2^fuel) : 
    (modPowAux m fuel b e res : ZMod m) = (res : ZMod m) * (b : ZMod m)^e := by
  induction fuel generalizing b e res with
  | zero => 
    have : e = 0 := by omega
    simp [this, modPowAux]
  | succ fuel ih =>
    rw [modPowAux]
    split_ifs with h_e h_odd
    · rw [h_e, pow_zero, mul_one]
    · have h1 : e / 2 < 2^fuel := by omega
      rw [ih _ _ _ h1]
      have he : e = 2 * (e / 2) + 1 := by omega
      rw [ZMod.natCast_mod, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_mul]
      nth_rw 2 [he]
      rw [pow_add, pow_one, pow_mul]
      ring
    · have h1 : e / 2 < 2^fuel := by omega
      rw [ih _ _ _ h1]
      have he : e = 2 * (e / 2) := by omega
      rw [ZMod.natCast_mod, Nat.cast_mul]
      nth_rw 2 [he]
      rw [pow_mul]
      ring

@[category API]
def modPow (base exp m : ℕ) : ℕ :=
  if m = 1 then 0 else modPowAux m 200 (base % m) exp 1

@[category API]
lemma pow_eq_modPow (b e m : ℕ) (hm : m > 1) (he : e < 2^200) :
    (b : ZMod m)^e = (modPow b e m : ZMod m) := by
  dsimp [modPow]
  have : ¬m = 1 := by omega
  simp [this]
  rw [modPowAux_spec _ _ _ _ _ he]
  push_cast
  rw [ZMod.natCast_mod]
  ring

@[category API]
lemma p6_factors (q : ℕ) (hq : q.Prime) (hdvd : q ∣ 2^8 * (3^2 * (7 * (17)))) :
    q = 2 ∨ q = 3 ∨ q = 7 ∨ q = 17 := by
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · left; exact Nat.prime_eq_prime_of_dvd_pow hq Nat.prime_two h
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · right; left; exact Nat.prime_eq_prime_of_dvd_pow hq Nat.prime_three h
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · right; right; left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
  · right; right; right; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp hdvd

@[category API]
lemma p6_prime : Nat.Prime 274177 := by
  apply lucas_primality 274177 5
  · change ((5 : ℕ) : ZMod 274177) ^ 274176 = 1
    rw [pow_eq_modPow]; decide; decide; decide
  · intro q hq hdvd
    change q ∣ 274176 at hdvd
    have h_eq : 274176 = 2^8 * (3^2 * (7 * (17))) := by rfl
    rw [h_eq] at hdvd
    rcases p6_factors q hq hdvd with rfl | rfl | rfl | rfl
    · change ((5 : ℕ) : ZMod 274177) ^ 137088 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((5 : ℕ) : ZMod 274177) ^ 91392 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((5 : ℕ) : ZMod 274177) ^ 39168 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((5 : ℕ) : ZMod 274177) ^ 16128 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide

@[category API]
lemma q6_4_2_2_factors (q : ℕ) (hq : q.Prime) (hdvd : q ∣ 2^4 * (3 * (347))) :
    q = 2 ∨ q = 3 ∨ q = 347 := by
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · left; exact Nat.prime_eq_prime_of_dvd_pow hq Nat.prime_two h
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · right; left; exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h
  · right; right; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp hdvd

@[category API]
lemma q6_4_2_2_prime : Nat.Prime 16657 := by
  apply lucas_primality 16657 5
  · change ((5 : ℕ) : ZMod 16657) ^ 16656 = 1
    rw [pow_eq_modPow]; decide; decide; decide
  · intro q hq hdvd
    change q ∣ 16656 at hdvd
    have h_eq : 16656 = 2^4 * (3 * (347)) := by rfl
    rw [h_eq] at hdvd
    rcases q6_4_2_2_factors q hq hdvd with rfl | rfl | rfl
    · change ((5 : ℕ) : ZMod 16657) ^ 8328 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((5 : ℕ) : ZMod 16657) ^ 5552 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((5 : ℕ) : ZMod 16657) ^ 48 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide

@[category API]
lemma q6_4_2_factors (q : ℕ) (hq : q.Prime) (hdvd : q ∣ 2 * (5 * (16657))) :
    q = 2 ∨ q = 5 ∨ q = 16657 := by
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · left; exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · right; left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
  · right; right; exact (Nat.prime_dvd_prime_iff_eq hq q6_4_2_2_prime).mp hdvd

@[category API]
lemma q6_4_2_prime : Nat.Prime 166571 := by
  apply lucas_primality 166571 2
  · change ((2 : ℕ) : ZMod 166571) ^ 166570 = 1
    rw [pow_eq_modPow]; decide; decide; decide
  · intro q hq hdvd
    change q ∣ 166570 at hdvd
    have h_eq : 166570 = 2 * (5 * (16657)) := by rfl
    rw [h_eq] at hdvd
    rcases q6_4_2_factors q hq hdvd with rfl | rfl | rfl
    · change ((2 : ℕ) : ZMod 166571) ^ 83285 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((2 : ℕ) : ZMod 166571) ^ 33314 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((2 : ℕ) : ZMod 166571) ^ 10 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide

@[category API]
lemma q6_4_factors (q : ℕ) (hq : q.Prime) (hdvd : q ∣ 2 * (3^2 * (166571))) :
    q = 2 ∨ q = 3 ∨ q = 166571 := by
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · left; exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · right; left; exact Nat.prime_eq_prime_of_dvd_pow hq Nat.prime_three h
  · right; right; exact (Nat.prime_dvd_prime_iff_eq hq q6_4_2_prime).mp hdvd

@[category API]
lemma q6_4_prime : Nat.Prime 2998279 := by
  apply lucas_primality 2998279 3
  · change ((3 : ℕ) : ZMod 2998279) ^ 2998278 = 1
    rw [pow_eq_modPow]; decide; decide; decide
  · intro q hq hdvd
    change q ∣ 2998278 at hdvd
    have h_eq : 2998278 = 2 * (3^2 * (166571)) := by rfl
    rw [h_eq] at hdvd
    rcases q6_4_factors q hq hdvd with rfl | rfl | rfl
    · change ((3 : ℕ) : ZMod 2998279) ^ 1499139 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((3 : ℕ) : ZMod 2998279) ^ 999426 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((3 : ℕ) : ZMod 2998279) ^ 18 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide

@[category API]
lemma q6_factors (q : ℕ) (hq : q.Prime) (hdvd : q ∣ 2^8 * (5 * (47 * (373 * (2998279))))) :
    q = 2 ∨ q = 5 ∨ q = 47 ∨ q = 373 ∨ q = 2998279 := by
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · left; exact Nat.prime_eq_prime_of_dvd_pow hq Nat.prime_two h
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · right; left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · right; right; left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · right; right; right; left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
  · right; right; right; right; exact (Nat.prime_dvd_prime_iff_eq hq q6_4_prime).mp hdvd

@[category API]
lemma q6_prime : Nat.Prime 67280421310721 := by
  apply lucas_primality 67280421310721 3
  · change ((3 : ℕ) : ZMod 67280421310721) ^ 67280421310720 = 1
    rw [pow_eq_modPow]; decide; decide; decide
  · intro q hq hdvd
    change q ∣ 67280421310720 at hdvd
    have h_eq : 67280421310720 = 2^8 * (5 * (47 * (373 * (2998279)))) := by rfl
    rw [h_eq] at hdvd
    rcases q6_factors q hq hdvd with rfl | rfl | rfl | rfl | rfl
    · change ((3 : ℕ) : ZMod 67280421310721) ^ 33640210655360 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((3 : ℕ) : ZMod 67280421310721) ^ 13456084262144 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((3 : ℕ) : ZMod 67280421310721) ^ 1431498325760 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((3 : ℕ) : ZMod 67280421310721) ^ 180376464640 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((3 : ℕ) : ZMod 67280421310721) ^ 22439680 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide

@[category API]
lemma p7_1_3_3_2_factors (q : ℕ) (hq : q.Prime) (hdvd : q ∣ 2^6 * (823)) :
    q = 2 ∨ q = 823 := by
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · left; exact Nat.prime_eq_prime_of_dvd_pow hq Nat.prime_two h
  · right; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp hdvd

@[category API]
lemma p7_1_3_3_2_prime : Nat.Prime 52673 := by
  apply lucas_primality 52673 3
  · change ((3 : ℕ) : ZMod 52673) ^ 52672 = 1
    rw [pow_eq_modPow]; decide; decide; decide
  · intro q hq hdvd
    change q ∣ 52672 at hdvd
    have h_eq : 52672 = 2^6 * (823) := by rfl
    rw [h_eq] at hdvd
    rcases p7_1_3_3_2_factors q hq hdvd with rfl | rfl
    · change ((3 : ℕ) : ZMod 52673) ^ 26336 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((3 : ℕ) : ZMod 52673) ^ 64 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide

@[category API]
lemma p7_1_3_3_factors (q : ℕ) (hq : q.Prime) (hdvd : q ∣ 2^2 * (3^2 * (52673))) :
    q = 2 ∨ q = 3 ∨ q = 52673 := by
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · left; exact Nat.prime_eq_prime_of_dvd_pow hq Nat.prime_two h
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · right; left; exact Nat.prime_eq_prime_of_dvd_pow hq Nat.prime_three h
  · right; right; exact (Nat.prime_dvd_prime_iff_eq hq p7_1_3_3_2_prime).mp hdvd

@[category API]
lemma p7_1_3_3_prime : Nat.Prime 1896229 := by
  apply lucas_primality 1896229 2
  · change ((2 : ℕ) : ZMod 1896229) ^ 1896228 = 1
    rw [pow_eq_modPow]; decide; decide; decide
  · intro q hq hdvd
    change q ∣ 1896228 at hdvd
    have h_eq : 1896228 = 2^2 * (3^2 * (52673)) := by rfl
    rw [h_eq] at hdvd
    rcases p7_1_3_3_factors q hq hdvd with rfl | rfl | rfl
    · change ((2 : ℕ) : ZMod 1896229) ^ 948114 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((2 : ℕ) : ZMod 1896229) ^ 632076 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((2 : ℕ) : ZMod 1896229) ^ 36 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide

@[category API]
lemma p7_1_3_factors (q : ℕ) (hq : q.Prime) (hdvd : q ∣ 2 * (3^3 * (181 * (1896229)))) :
    q = 2 ∨ q = 3 ∨ q = 181 ∨ q = 1896229 := by
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · left; exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · right; left; exact Nat.prime_eq_prime_of_dvd_pow hq Nat.prime_three h
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · right; right; left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
  · right; right; right; exact (Nat.prime_dvd_prime_iff_eq hq p7_1_3_3_prime).mp hdvd

@[category API]
lemma p7_1_3_prime : Nat.Prime 18533742247 := by
  apply lucas_primality 18533742247 6
  · change ((6 : ℕ) : ZMod 18533742247) ^ 18533742246 = 1
    rw [pow_eq_modPow]; decide; decide; decide
  · intro q hq hdvd
    change q ∣ 18533742246 at hdvd
    have h_eq : 18533742246 = 2 * (3^3 * (181 * (1896229))) := by rfl
    rw [h_eq] at hdvd
    rcases p7_1_3_factors q hq hdvd with rfl | rfl | rfl | rfl
    · change ((6 : ℕ) : ZMod 18533742247) ^ 9266871123 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((6 : ℕ) : ZMod 18533742247) ^ 6177914082 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((6 : ℕ) : ZMod 18533742247) ^ 102396366 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((6 : ℕ) : ZMod 18533742247) ^ 9774 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide

@[category API]
lemma p7_1_factors (q : ℕ) (hq : q.Prime) (hdvd : q ∣ 2 * (7 * (449 * (18533742247)))) :
    q = 2 ∨ q = 7 ∨ q = 449 ∨ q = 18533742247 := by
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · left; exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · right; left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · right; right; left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
  · right; right; right; exact (Nat.prime_dvd_prime_iff_eq hq p7_1_3_prime).mp hdvd

@[category API]
lemma p7_1_prime : Nat.Prime 116503103764643 := by
  apply lucas_primality 116503103764643 2
  · change ((2 : ℕ) : ZMod 116503103764643) ^ 116503103764642 = 1
    rw [pow_eq_modPow]; decide; decide; decide
  · intro q hq hdvd
    change q ∣ 116503103764642 at hdvd
    have h_eq : 116503103764642 = 2 * (7 * (449 * (18533742247))) := by rfl
    rw [h_eq] at hdvd
    rcases p7_1_factors q hq hdvd with rfl | rfl | rfl | rfl
    · change ((2 : ℕ) : ZMod 116503103764643) ^ 58251551882321 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((2 : ℕ) : ZMod 116503103764643) ^ 16643300537806 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((2 : ℕ) : ZMod 116503103764643) ^ 259472391458 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((2 : ℕ) : ZMod 116503103764643) ^ 6286 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide

@[category API]
lemma p7_factors (q : ℕ) (hq : q.Prime) (hdvd : q ∣ 2^9 * (116503103764643)) :
    q = 2 ∨ q = 116503103764643 := by
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · left; exact Nat.prime_eq_prime_of_dvd_pow hq Nat.prime_two h
  · right; exact (Nat.prime_dvd_prime_iff_eq hq p7_1_prime).mp hdvd

@[category API]
lemma p7_prime : Nat.Prime 59649589127497217 := by
  apply lucas_primality 59649589127497217 3
  · change ((3 : ℕ) : ZMod 59649589127497217) ^ 59649589127497216 = 1
    rw [pow_eq_modPow]; decide; decide; decide
  · intro q hq hdvd
    change q ∣ 59649589127497216 at hdvd
    have h_eq : 59649589127497216 = 2^9 * (116503103764643) := by rfl
    rw [h_eq] at hdvd
    rcases p7_factors q hq hdvd with rfl | rfl
    · change ((3 : ℕ) : ZMod 59649589127497217) ^ 29824794563748608 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((3 : ℕ) : ZMod 59649589127497217) ^ 512 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide

@[category API]
lemma q7_3_factors (q : ℕ) (hq : q.Prime) (hdvd : q ∣ 2^4 * (11 * (71))) :
    q = 2 ∨ q = 11 ∨ q = 71 := by
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · left; exact Nat.prime_eq_prime_of_dvd_pow hq Nat.prime_two h
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · right; left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
  · right; right; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp hdvd

@[category API]
lemma q7_3_prime : Nat.Prime 12497 := by
  apply lucas_primality 12497 3
  · change ((3 : ℕ) : ZMod 12497) ^ 12496 = 1
    rw [pow_eq_modPow]; decide; decide; decide
  · intro q hq hdvd
    change q ∣ 12496 at hdvd
    have h_eq : 12496 = 2^4 * (11 * (71)) := by rfl
    rw [h_eq] at hdvd
    rcases q7_3_factors q hq hdvd with rfl | rfl | rfl
    · change ((3 : ℕ) : ZMod 12497) ^ 6248 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((3 : ℕ) : ZMod 12497) ^ 1136 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((3 : ℕ) : ZMod 12497) ^ 176 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide

@[category API]
lemma q7_4_2_factors (q : ℕ) (hq : q.Prime) (hdvd : q ∣ 2 * (3 * (367))) :
    q = 2 ∨ q = 3 ∨ q = 367 := by
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · left; exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · right; left; exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h
  · right; right; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp hdvd

@[category API]
lemma q7_4_2_prime : Nat.Prime 2203 := by
  apply lucas_primality 2203 5
  · change ((5 : ℕ) : ZMod 2203) ^ 2202 = 1
    rw [pow_eq_modPow]; decide; decide; decide
  · intro q hq hdvd
    change q ∣ 2202 at hdvd
    have h_eq : 2202 = 2 * (3 * (367)) := by rfl
    rw [h_eq] at hdvd
    rcases q7_4_2_factors q hq hdvd with rfl | rfl | rfl
    · change ((5 : ℕ) : ZMod 2203) ^ 1101 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((5 : ℕ) : ZMod 2203) ^ 734 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((5 : ℕ) : ZMod 2203) ^ 6 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide

@[category API]
lemma q7_4_3_1_3_factors (q : ℕ) (hq : q.Prime) (hdvd : q ∣ 2 * (3^4 * (11))) :
    q = 2 ∨ q = 3 ∨ q = 11 := by
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · left; exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · right; left; exact Nat.prime_eq_prime_of_dvd_pow hq Nat.prime_three h
  · right; right; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp hdvd

@[category API]
lemma q7_4_3_1_3_prime : Nat.Prime 1783 := by
  apply lucas_primality 1783 10
  · change ((10 : ℕ) : ZMod 1783) ^ 1782 = 1
    rw [pow_eq_modPow]; decide; decide; decide
  · intro q hq hdvd
    change q ∣ 1782 at hdvd
    have h_eq : 1782 = 2 * (3^4 * (11)) := by rfl
    rw [h_eq] at hdvd
    rcases q7_4_3_1_3_factors q hq hdvd with rfl | rfl | rfl
    · change ((10 : ℕ) : ZMod 1783) ^ 891 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((10 : ℕ) : ZMod 1783) ^ 594 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((10 : ℕ) : ZMod 1783) ^ 162 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide

@[category API]
lemma q7_4_3_1_factors (q : ℕ) (hq : q.Prime) (hdvd : q ∣ 2^2 * (7 * (139 * (1783)))) :
    q = 2 ∨ q = 7 ∨ q = 139 ∨ q = 1783 := by
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · left; exact Nat.prime_eq_prime_of_dvd_pow hq Nat.prime_two h
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · right; left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · right; right; left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
  · right; right; right; exact (Nat.prime_dvd_prime_iff_eq hq q7_4_3_1_3_prime).mp hdvd

@[category API]
lemma q7_4_3_1_prime : Nat.Prime 6939437 := by
  apply lucas_primality 6939437 2
  · change ((2 : ℕ) : ZMod 6939437) ^ 6939436 = 1
    rw [pow_eq_modPow]; decide; decide; decide
  · intro q hq hdvd
    change q ∣ 6939436 at hdvd
    have h_eq : 6939436 = 2^2 * (7 * (139 * (1783))) := by rfl
    rw [h_eq] at hdvd
    rcases q7_4_3_1_factors q hq hdvd with rfl | rfl | rfl | rfl
    · change ((2 : ℕ) : ZMod 6939437) ^ 3469718 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((2 : ℕ) : ZMod 6939437) ^ 991348 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((2 : ℕ) : ZMod 6939437) ^ 49924 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((2 : ℕ) : ZMod 6939437) ^ 3892 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide

@[category API]
lemma q7_4_3_factors (q : ℕ) (hq : q.Prime) (hdvd : q ∣ 2^3 * (6939437)) :
    q = 2 ∨ q = 6939437 := by
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · left; exact Nat.prime_eq_prime_of_dvd_pow hq Nat.prime_two h
  · right; exact (Nat.prime_dvd_prime_iff_eq hq q7_4_3_1_prime).mp hdvd

@[category API]
lemma q7_4_3_prime : Nat.Prime 55515497 := by
  apply lucas_primality 55515497 3
  · change ((3 : ℕ) : ZMod 55515497) ^ 55515496 = 1
    rw [pow_eq_modPow]; decide; decide; decide
  · intro q hq hdvd
    change q ∣ 55515496 at hdvd
    have h_eq : 55515496 = 2^3 * (6939437) := by rfl
    rw [h_eq] at hdvd
    rcases q7_4_3_factors q hq hdvd with rfl | rfl
    · change ((3 : ℕ) : ZMod 55515497) ^ 27757748 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((3 : ℕ) : ZMod 55515497) ^ 8 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide

@[category API]
lemma q7_4_factors (q : ℕ) (hq : q.Prime) (hdvd : q ∣ 2 * (3 * (2203 * (55515497)))) :
    q = 2 ∨ q = 3 ∨ q = 2203 ∨ q = 55515497 := by
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · left; exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · right; left; exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · right; right; left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
  · right; right; right; exact (Nat.prime_dvd_prime_iff_eq hq q7_4_3_prime).mp hdvd

@[category API]
lemma q7_4_prime : Nat.Prime 733803839347 := by
  apply lucas_primality 733803839347 2
  · change ((2 : ℕ) : ZMod 733803839347) ^ 733803839346 = 1
    rw [pow_eq_modPow]; decide; decide; decide
  · intro q hq hdvd
    change q ∣ 733803839346 at hdvd
    have h_eq : 733803839346 = 2 * (3 * (2203 * (55515497))) := by rfl
    rw [h_eq] at hdvd
    rcases q7_4_factors q hq hdvd with rfl | rfl | rfl | rfl
    · change ((2 : ℕ) : ZMod 733803839347) ^ 366901919673 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((2 : ℕ) : ZMod 733803839347) ^ 244601279782 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((2 : ℕ) : ZMod 733803839347) ^ 333092982 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((2 : ℕ) : ZMod 733803839347) ^ 13218 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide

@[category API]
lemma q7_factors (q : ℕ) (hq : q.Prime) (hdvd : q ∣ 2^9 * (3^5 * (5 * (12497 * (733803839347))))) :
    q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 12497 ∨ q = 733803839347 := by
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · left; exact Nat.prime_eq_prime_of_dvd_pow hq Nat.prime_two h
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · right; left; exact Nat.prime_eq_prime_of_dvd_pow hq Nat.prime_three h
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · right; right; left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · right; right; right; left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
  · right; right; right; right; exact (Nat.prime_dvd_prime_iff_eq hq q7_4_prime).mp hdvd

@[category API]
lemma q7_prime : Nat.Prime 5704689200685129054721 := by
  apply lucas_primality 5704689200685129054721 21
  · change ((21 : ℕ) : ZMod 5704689200685129054721) ^ 5704689200685129054720 = 1
    rw [pow_eq_modPow]; decide; decide; decide
  · intro q hq hdvd
    change q ∣ 5704689200685129054720 at hdvd
    have h_eq : 5704689200685129054720 = 2^9 * (3^5 * (5 * (12497 * (733803839347)))) := by rfl
    rw [h_eq] at hdvd
    rcases q7_factors q hq hdvd with rfl | rfl | rfl | rfl | rfl
    · change ((21 : ℕ) : ZMod 5704689200685129054721) ^ 2852344600342564527360 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((21 : ℕ) : ZMod 5704689200685129054721) ^ 1901563066895043018240 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((21 : ℕ) : ZMod 5704689200685129054721) ^ 1140937840137025810944 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((21 : ℕ) : ZMod 5704689200685129054721) ^ 456484692380981760 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((21 : ℕ) : ZMod 5704689200685129054721) ^ 7774133760 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide



@[category API, AMS 11]
lemma a_def (n : ℕ) : a n = 2^n - log2 (minFac (fermatNumber n)) := rfl

@[category API, AMS 11]
lemma minFac_eq_of_mul (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (h_le : p ≤ q) :
    (p * q).minFac = p := by
  have h1 : 1 < p * q := by nlinarith [hp.two_le, hq.two_le]
  have hm_prime : (p * q).minFac.Prime := minFac_prime h1.ne'
  have hdvd_pq : (p * q).minFac ∣ p * q := minFac_dvd (p * q)
  have h_le_p : (p * q).minFac ≤ p := minFac_le_of_dvd hp.two_le (dvd_mul_right p q)
  rcases hm_prime.dvd_mul.mp hdvd_pq with hpq | hqq
  · exact (Nat.prime_dvd_prime_iff_eq hm_prime hp).mp hpq
  · have := (Nat.prime_dvd_prime_iff_eq hm_prime hq).mp hqq
    omega

@[category test, AMS 11]
theorem six : a 6 = 46 := by
  rw [a_def]
  have h_minFac : minFac (fermatNumber 6) = 274177 := by
    have h_eq : fermatNumber 6 = 274177 * 67280421310721 := by decide
    rw [h_eq]
    exact minFac_eq_of_mul _ _ p6_prime q6_prime (by decide)
  rw [h_minFac]
  decide

@[category test, AMS 11]
theorem seven : a 7 = 73 := by
  rw [a_def]
  have h_minFac : minFac (fermatNumber 7) = 59649589127497217 := by
    have h_eq : fermatNumber 7 = 59649589127497217 * 5704689200685129054721 := by decide
    rw [h_eq]
    exact minFac_eq_of_mul _ _ p7_prime q7_prime (by decide)
  rw [h_minFac]
  decide

/--
Conjecture: the dyadic valuation of A93179(n) - 1 does not exceed 2^n - a(n).

A93179(n) is minFac(fermatNumber n), the smallest prime factor of the n-th Fermat number.
The conjecture states that if $P_n$ is the smallest prime factor of the $n$-th Fermat number,
then $\nu_2(P_n - 1) \le 2^n - a(n)$.
Substituting the definition of $a(n)$, this is equivalent to $\nu_2(P_n - 1) \le \lfloor \log_2(P_n) \rfloor$.

This is Conjecture 3.4 in [SA22].
-/
@[category research solved, AMS 11]
theorem oeis_358684_conjecture_0 (n : ℕ) :
    padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n := by
  delta fermatNumber and a
  rw [Nat.sub_sub_self]
  · rw [Nat.log2_eq_log_two]
    apply Nat.le_log_of_pow_le (by decide)
    refine le_trans ?_ <| sub_le _ 1
    apply Nat.ordProj_le 2
    exact Nat.sub_ne_zero_of_lt (Nat.minFac_prime (by norm_num)).one_lt
  · rw [Nat.log2_eq_log_two]
    have : (2 ^ 2 ^ n) + 1 < 2 ^ ((2 ^ n) + 1) := by
      simp [pow_add, mul_two]
    refine Nat.le_of_lt_succ <| (2).log_lt_of_lt_pow ?_ ?_
    · exact Nat.minFac_pos _|>.ne'
    · exact (Nat.minFac_le (by bound)).trans_lt this

end OeisA358684
