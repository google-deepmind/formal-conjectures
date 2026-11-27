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
# Recurrence involving LCM: $a(n) = x(n+1)/x(n) - 2$

$a(n) = x(n+1)/x(n) - 2$ where $x(1)=1$ and $x(n) = 2 x(n-1) + \operatorname{lcm}(x(n-1),n)$
for $n > 1$.

*References:*
- [A135508](https://oeis.org/A135508)-/

@[expose] public section

namespace OeisA135508

/-- Auxiliary sequence $x(n)$ with $x(1)=1$ and $x(n) = 2 x(n-1) + \operatorname{lcm}(x(n-1),n)$. -/
def x : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 1 => 2 * x n + Nat.lcm (x n) (n + 1)

/-- $a(n) = x(n+1)/x(n) - 2$ for $n \ge 1$, and $a(0) = 0$. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else (x (n + 1) / x n) - 2

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by rfl

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by rfl

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by rfl

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by rfl

/--
Conjecture: For prime $p$ such that $p-2$ is not a prime, $a(p-1) = p$.
- _Bill McEachen_, Sep 26 2025
-/
@[category research open, AMS 11]
theorem conjecture (p : ℕ) (hp : p.Prime) (hp_twin : ¬ (p - 2).Prime) : a (p - 1) = p := by
  sorry

/-- `b n = (n + 1) / gcd(x n, n + 1)`; for `n ≥ 1` this equals `a n`. -/
def b (n : ℕ) : ℕ := (n + 1) / Nat.gcd (x n) (n + 1)

/-- The defining recurrence for `n ≥ 1`. -/
@[category API, AMS 11]
lemma x_succ {n : ℕ} (hn : 1 ≤ n) : x (n + 1) = 2 * x n + Nat.lcm (x n) (n + 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rfl

/-- `x (n + 1) = x n * (2 + b n)` for `n ≥ 1`. -/
@[category API, AMS 11]
lemma x_succ_eq {n : ℕ} (hn : 1 ≤ n) : x (n + 1) = x n * (2 + b n) := by
  rw [x_succ hn, Nat.lcm, b, Nat.mul_div_assoc _ (Nat.gcd_dvd_right _ _)]
  ring

/-- `x n > 0` for `n ≥ 1`. -/
@[category API, AMS 11]
lemma x_pos : ∀ {n : ℕ}, 1 ≤ n → 0 < x n
  | 1, _ => Nat.one_pos
  | n + 2, _ => by
    rw [x_succ_eq (by omega)]
    have := x_pos (n := n + 1) (by omega)
    positivity

/-- `a n = (n + 1) / gcd(x n, n + 1)` for `n ≥ 1`. -/
@[category API, AMS 11]
lemma a_eq_b {n : ℕ} (hn : 1 ≤ n) : a n = b n := by
  rw [a, if_neg (by omega), x_succ_eq hn, Nat.mul_div_cancel_left _ (x_pos hn)]
  omega

/-- `x n ∣ x m` for `1 ≤ n ≤ m`. -/
@[category API, AMS 11]
lemma x_dvd_x {n m : ℕ} (hn : 1 ≤ n) (h : n ≤ m) : x n ∣ x m := by
  induction m, h using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    rw [x_succ_eq (by omega)]
    exact Dvd.dvd.mul_right ih _

/-- A prime dividing `x n` divides `2 + b j` for some `1 ≤ j < n`. -/
@[category API, AMS 11]
lemma exists_of_prime_dvd_x {p : ℕ} (hp : p.Prime) :
    ∀ {n : ℕ}, 1 ≤ n → p ∣ x n → ∃ j, 1 ≤ j ∧ j < n ∧ p ∣ 2 + b j
  | 1, _, h => absurd (Nat.dvd_one.mp h) hp.ne_one
  | n + 2, _, h => by
    rw [x_succ_eq (by omega)] at h
    rcases hp.dvd_mul.mp h with h | h
    · obtain ⟨j, h1, h2, h3⟩ := exists_of_prime_dvd_x hp (by omega) h
      exact ⟨j, h1, by omega, h3⟩
    · exact ⟨n + 1, by omega, by omega, h⟩

/-- **Reduction.** If `p ≥ 5` is prime and some prime factor `q` of `p - 2` already divides
`x (p - 3)`, then `a (p - 1) = p`. -/
@[category research solved, AMS 11]
theorem a_pred_eq_self {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : q.Prime)
    (hqc : q ∣ p - 2) (hqx : q ∣ x (p - 3)) : a (p - 1) = p := by
  have hnd : ¬ p ∣ x (p - 1) := by
    intro h
    obtain ⟨j, hj1, hjp, hdvd⟩ := exists_of_prime_dvd_x hp (by omega) h
    set g := Nat.gcd (x j) (j + 1) with hg_def
    have hg0 : 0 < g := Nat.gcd_pos_of_pos_right _ (by omega)
    have hg : b j * g = j + 1 := Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)
    have hble : b j ≤ j + 1 := Nat.div_le_self _ _
    have heq : 2 + b j = p :=
      Nat.eq_of_dvd_of_lt_two_mul (by omega) hdvd (by omega)
    have hg1 : g = 1 := by
      by_contra hne
      have : (p - 2) * 2 ≤ (p - 2) * g := Nat.mul_le_mul_left _ (by omega)
      have : (p - 2) * g = j + 1 := by rw [← hg]; congr 1; omega
      omega
    have hj : j = p - 3 := by rw [hg1, mul_one] at hg; omega
    have hqg : q ∣ g := Nat.dvd_gcd (hj ▸ hqx) (by rw [hj, show p - 3 + 1 = p - 2 by omega]; exact hqc)
    rw [hg1] at hqg
    exact hq.one_lt.ne' (Nat.dvd_one.mp hqg)
  have hcop : Nat.gcd (x (p - 1)) p = 1 :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd)
  rw [a_eq_b (by omega), b, Nat.sub_add_cancel (by omega), hcop, Nat.div_one]

/-- `x 3 = 20`. -/
@[category API, AMS 11]
lemma x_three : x 3 = 20 := by decide
/-- `x 4 = 60`. -/
@[category API, AMS 11]
lemma x_four : x 4 = 60 := by decide

/-- The conjecture holds for every prime `p ≡ 2 (mod 3)`. -/
@[category research solved, AMS 11]
theorem conjecture.variants.mod_three {p : ℕ} (hp : p.Prime) (hp_twin : ¬ (p - 2).Prime)
    (h3 : p % 3 = 2) : a (p - 1) = p := by
  rcases (by omega : p = 2 ∨ p = 5 ∨ 11 ≤ p ∨ (5 < p ∧ p < 11)) with rfl | rfl | h | h
  · decide
  · exact absurd Nat.prime_three hp_twin
  · refine a_pred_eq_self hp (by omega) Nat.prime_three (by omega) ?_
    exact (show 3 ∣ x 4 by rw [x_four]; norm_num).trans (x_dvd_x (by norm_num) (by omega))
  · obtain rfl : p = 8 := by omega
    exact absurd hp (by decide)

/-- The conjecture holds for every prime `p ≡ 2 (mod 5)`. -/
@[category research solved, AMS 11]
theorem conjecture.variants.mod_five {p : ℕ} (hp : p.Prime) (hp_twin : ¬ (p - 2).Prime)
    (h5 : p % 5 = 2) : a (p - 1) = p := by
  rcases (by omega : p = 2 ∨ p = 7 ∨ 12 ≤ p ∨ (2 < p ∧ p < 12 ∧ p ≠ 7)) with rfl | rfl | h | h
  · decide
  · exact absurd Nat.prime_five hp_twin
  · refine a_pred_eq_self hp (by omega) Nat.prime_five (by omega) ?_
    exact (show 5 ∣ x 3 by rw [x_three]; norm_num).trans (x_dvd_x (by norm_num) (by omega))
  · omega

/-- The conjecture follows from: every prime `q` divides `x (q ^ 2 - 1)`. -/
@[category research solved, AMS 11]
theorem conjecture.variants.of_forall_prime_dvd (H : ∀ q, q.Prime → q ∣ x (q ^ 2 - 1))
    {p : ℕ} (hp : p.Prime) (hp_twin : ¬ (p - 2).Prime) : a (p - 1) = p := by
  rcases (by have := hp.two_le; omega : p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p) with rfl | rfl | rfl | h
  · decide
  · decide
  · exact absurd hp (by decide)
  · have hc1 : p - 2 ≠ 1 := by omega
    have hq := Nat.minFac_prime hc1
    have hsq := Nat.minFac_sq_le_self (by omega : 0 < p - 2) hp_twin
    have h2 : 2 ≤ (p - 2).minFac := hq.two_le
    refine a_pred_eq_self hp h hq (Nat.minFac_dvd _) ((H _ hq).trans (x_dvd_x ?_ (by omega)))
    have : 4 ≤ (p - 2).minFac ^ 2 := by nlinarith
    omega

/-- **Exact reduction.** For a prime `p ≥ 5`, if `x (p - 3)` is coprime to `p - 2` then
`a (p - 1) ≠ p`. Together with `a_pred_eq_self`, `a (p - 1) = p` holds iff `p - 2` shares a
prime factor with `x (p - 3)`. -/
@[category research solved, AMS 11]
theorem a_pred_ne_self {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hcop : Nat.Coprime (x (p - 3)) (p - 2)) : a (p - 1) ≠ p := by
  have hb : b (p - 3) = p - 2 := by
    rw [b, show p - 3 + 1 = p - 2 by omega, hcop, Nat.div_one]
  have hpx : p ∣ x (p - 1) := by
    have h := x_succ_eq (n := p - 3) (by omega)
    rw [hb, show 2 + (p - 2) = p by omega, show p - 3 + 1 = p - 2 by omega] at h
    exact (h ▸ dvd_mul_left p _).trans (x_dvd_x (by omega) (by omega))
  rw [a_eq_b (by omega), b, Nat.sub_add_cancel (by omega),
    Nat.gcd_eq_right hpx, Nat.div_self hp.pos]
  exact hp.one_lt.ne

set_option maxRecDepth 100000 in
/-- Every prime `q < 100` divides `x (q ^ 2 - 1)` (checked by computation). -/
@[category API, AMS 11]
lemma prime_dvd_x_sq_sub_one_of_lt {q : ℕ} (hq : q.Prime) (h : q < 100) :
    q ∣ x (q ^ 2 - 1) := by
  have key : ∀ N, 1 ≤ N → N ≤ q ^ 2 - 1 → q ∣ x N → q ∣ x (q ^ 2 - 1) :=
    fun N h1 h2 hN => hN.trans (x_dvd_x h1 h2)
  interval_cases q
  all_goals try (exfalso; revert hq; decide)
  · exact key 2 (by norm_num) (by norm_num) (by decide)
  · exact key 4 (by norm_num) (by norm_num) (by decide)
  · exact key 3 (by norm_num) (by norm_num) (by decide)
  · exact key 47 (by norm_num) (by norm_num) (by decide)
  · exact key 53 (by norm_num) (by norm_num) (by decide)
  · exact key 11 (by norm_num) (by norm_num) (by decide)
  · exact key 83 (by norm_num) (by norm_num) (by decide)
  · exact key 17 (by norm_num) (by norm_num) (by decide)
  · exact key 67 (by norm_num) (by norm_num) (by decide)
  · exact key 317 (by norm_num) (by norm_num) (by decide)
  · exact key 29 (by norm_num) (by norm_num) (by decide)
  · exact key 257 (by norm_num) (by norm_num) (by decide)
  · exact key 367 (by norm_num) (by norm_num) (by decide)
  · exact key 41 (by norm_num) (by norm_num) (by decide)
  · exact key 233 (by norm_num) (by norm_num) (by decide)
  · exact key 157 (by norm_num) (by norm_num) (by decide)
  · exact key 293 (by norm_num) (by norm_num) (by decide)
  · exact key 59 (by norm_num) (by norm_num) (by decide)
  · exact key 467 (by norm_num) (by norm_num) (by decide)
  · exact key 211 (by norm_num) (by norm_num) (by decide)
  · exact key 71 (by norm_num) (by norm_num) (by decide)
  · exact key 709 (by norm_num) (by norm_num) (by decide)
  · exact key 911 (by norm_num) (by norm_num) (by decide)
  · exact key 443 (by norm_num) (by norm_num) (by decide)
  · exact key 677 (by norm_num) (by norm_num) (by decide)


/-- `lcm(100, …, 433)`. -/
def L₁ : ℕ := 322158800202316016441916052210562304094187196824039642931402735639952623350986594345884325036074891474893025590144901399961380572701419623962592800681491782010438052744491503511181138464000

/-- `lcm(434, …, 999)`. -/
def L₂ : ℕ := 7128865274665093053166384155714272920668358861885893040452001991154324087581111499476444151913871586911717817019575256512980264067621009251465871004305131072686268143200196609974862745937188343705015434452523739745298963145674982128236956232823794011068809262317708861979540791247754558049326475737829923352751796735248042463638051137034331214781746850878453485678021888075373249921995672056932029099390891687487672697950931603520000

/-- Every `n ∈ [100, 433]` divides `L₁`. -/
@[category API, AMS 11]
lemma dvd_L₁ : ∀ n < 434, 100 ≤ n → n ∣ L₁ := by decide +kernel

/-- Every `n ∈ [434, 999]` divides `L₂`. -/
@[category API, AMS 11]
lemma dvd_L₂ : ∀ n < 1000, 434 ≤ n → n ∣ L₂ := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Computation: `lcm(100, …, 433)` divides `x 7121`. -/
@[category API, AMS 11]
lemma L₁_dvd_x : L₁ ∣ x 7121 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Computation: `lcm(434, …, 999)` divides `x 42611`. -/
@[category API, AMS 11]
lemma L₂_dvd_x : L₂ ∣ x 42611 := by decide +kernel

/-- Every prime `q < 1000` divides `x (q ^ 2 - 1)`. -/
@[category API, AMS 11]
lemma prime_dvd_x_sq_sub_one_of_lt_1000 {q : ℕ} (hq : q.Prime) (h : q < 1000) :
    q ∣ x (q ^ 2 - 1) := by
  rcases (by omega : q < 100 ∨ (100 ≤ q ∧ q ≤ 433) ∨ 434 ≤ q) with h1 | ⟨h1, h2⟩ | h1
  · exact prime_dvd_x_sq_sub_one_of_lt hq h1
  · refine ((dvd_L₁ q (by omega) h1).trans L₁_dvd_x).trans
      (x_dvd_x (by norm_num) ?_)
    have : 10000 ≤ q ^ 2 := by nlinarith
    omega
  · refine ((dvd_L₂ q h h1).trans L₂_dvd_x).trans
      (x_dvd_x (by norm_num) ?_)
    have : 434 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left h1 2
    omega

/-- The conjecture holds whenever the least prime factor of `p - 2` is less than `1000`. -/
@[category research solved, AMS 11]
theorem conjecture.variants.minFac_lt {p : ℕ} (hp : p.Prime) (hp_twin : ¬ (p - 2).Prime)
    (h : (p - 2).minFac < 1000) : a (p - 1) = p := by
  rcases (by have := hp.two_le; omega : p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p) with rfl | rfl | rfl | h5
  · decide
  · decide
  · exact absurd hp (by decide)
  · have hq := Nat.minFac_prime (show p - 2 ≠ 1 by omega)
    have hsq := Nat.minFac_sq_le_self (by omega : 0 < p - 2) hp_twin
    have h2 : 2 ≤ (p - 2).minFac := hq.two_le
    refine a_pred_eq_self hp h5 hq (Nat.minFac_dvd _)
      ((prime_dvd_x_sq_sub_one_of_lt_1000 hq h).trans (x_dvd_x ?_ (by omega)))
    have : 4 ≤ (p - 2).minFac ^ 2 := by nlinarith
    omega

/-- The conjecture holds for every prime `p < 10 ^ 6 + 2`. -/
@[category research solved, AMS 11]
theorem conjecture.variants.lt {p : ℕ} (hp : p.Prime) (hp_twin : ¬ (p - 2).Prime)
    (hlt : p < 10 ^ 6 + 2) : a (p - 1) = p := by
  rcases (by have := hp.two_le; omega : p ≤ 4 ∨ 5 ≤ p) with h4 | h5
  · have := hp.two_le
    interval_cases p
    · decide
    · decide
    · exact absurd hp (by decide)
  · refine conjecture.variants.minFac_lt hp hp_twin ?_
    have hsq := Nat.minFac_sq_le_self (by omega : 0 < p - 2) hp_twin
    by_contra h
    have : 1000 ^ 2 ≤ (p - 2).minFac ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega

end OeisA135508
