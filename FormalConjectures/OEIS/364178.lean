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
# Factorial ratio $\frac{(10n)! (3n)! (n/2)!}{(6n)! (5n)! (3n/2)! n!}$

The sequence is defined for even $n = 2m$ by
$$a(n) = \frac{(10n)! (3n)! (n/2)!}{(6n)! (5n)! (3n/2)! n!}$$

*References:*
- [A364178](https://oeis.org/A364178)
-/
open Real
open Nat

namespace OeisA364178

/--
The sequence $a(n) = \frac{(10n)! (3n)! (n/2)!}{(6n)! (5n)! (3n/2)! n!}$ for even $n$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  (round
    ((Gamma (10 * (↑n : ℝ) + 1) * Gamma (3 * (↑n : ℝ) + 1) * Gamma ((↑n : ℝ) / 2 + 1)) /
     (Gamma (6 * (↑n : ℝ) + 1) * Gamma (5 * (↑n : ℝ) + 1) *
      Gamma (3 * (↑n : ℝ) / 2 + 1) * Gamma (↑n + 1)))
  ).toNat

@[category API, AMS 11]
lemma gamma_three_halves : Gamma (1 / 2 + 1) = (1 / 2) * √Real.pi := by
  rw [Gamma_add_one (by norm_num), Gamma_one_half_eq]

@[category API, AMS 11]
lemma gamma_five_halves : Gamma (3 / 2 + 1) = (3 / 4) * √Real.pi := by
  rw [Gamma_add_one (by norm_num), show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
      Gamma_add_one (by norm_num), Gamma_one_half_eq]
  ring

@[category API, AMS 11]
lemma gamma_eleven_halves : Gamma (9 / 2 + 1) = (945 / 32) * √Real.pi := by
  rw [Gamma_add_one (by norm_num), show (9 / 2 : ℝ) = 7 / 2 + 1 by norm_num]
  rw [Gamma_add_one (by norm_num), show (7 / 2 : ℝ) = 5 / 2 + 1 by norm_num]
  rw [Gamma_add_one (by norm_num), show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num]
  rw [Gamma_add_one (by norm_num), show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num]
  rw [Gamma_add_one (by norm_num), Gamma_one_half_eq]
  ring

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by
  unfold a; push_cast; norm_num [Real.Gamma_one]

@[category test, AMS 11]
theorem a_1 : a 1 = 168 := by
  unfold a; push_cast
  have h10 : (10 * (1 : ℝ) + 1) = ((10 : ℕ) : ℝ) + 1 := by norm_num
  have h3 : (3 * (1 : ℝ) + 1) = ((3 : ℕ) : ℝ) + 1 := by norm_num
  have h6 : (6 * (1 : ℝ) + 1) = ((6 : ℕ) : ℝ) + 1 := by norm_num
  have h5 : (5 * (1 : ℝ) + 1) = ((5 : ℕ) : ℝ) + 1 := by norm_num
  have h1 : ((1 : ℝ) + 1) = ((1 : ℕ) : ℝ) + 1 := by norm_num
  have h12 : (1 : ℝ) / 2 + 1 = 1 / 2 + 1 := by ring
  have h32 : 3 * (1 : ℝ) / 2 + 1 = 3 / 2 + 1 := by ring
  rw [h10, h3, h6, h5, h1, h12, h32]
  rw [Real.Gamma_nat_eq_factorial 10, Real.Gamma_nat_eq_factorial 3,
      Real.Gamma_nat_eq_factorial 6, Real.Gamma_nat_eq_factorial 5,
      Real.Gamma_nat_eq_factorial 1]
  rw [gamma_three_halves, gamma_five_halves]
  have hpi : √Real.pi ≠ 0 := by positivity
  have h_cancel : 21772800 * (1 / 2 * √Real.pi) / (86400 * (3 / 4 * √Real.pi)) = 168 := by
    calc 21772800 * (1 / 2 * √Real.pi) / (86400 * (3 / 4 * √Real.pi))
      _ = (21772800 * (1 / 2) * √Real.pi) / (86400 * (3 / 4) * √Real.pi) := by ring
      _ = 10886400 * √Real.pi / (64800 * √Real.pi) := by norm_num
      _ = (10886400 / 64800) * (√Real.pi / √Real.pi) := by ring
      _ = 168 * 1 := by rw [div_self hpi]; norm_num
      _ = 168 := by norm_num
  rw [show (Nat.factorial 10 : ℝ) * ↑(Nat.factorial 3) = 21772800 by norm_num]
  rw [
      show (Nat.factorial 6 : ℝ) * ↑(Nat.factorial 5) * (3 / 4 * √Real.pi) * ↑(Nat.factorial 1) =
        86400 * (3 / 4 * √Real.pi) by ring]
  rw [h_cancel]
  norm_num; rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 83980 := by
  unfold a; push_cast
  have h20 : (10 * (2 : ℝ) + 1) = ((20 : ℕ) : ℝ) + 1 := by norm_num
  have h6 : (3 * (2 : ℝ) + 1) = ((6 : ℕ) : ℝ) + 1 := by norm_num
  have h1 : ((2 : ℝ) / 2 + 1) = ((1 : ℕ) : ℝ) + 1 := by norm_num
  have h12 : (6 * (2 : ℝ) + 1) = ((12 : ℕ) : ℝ) + 1 := by norm_num
  have h10 : (5 * (2 : ℝ) + 1) = ((10 : ℕ) : ℝ) + 1 := by norm_num
  have h3 : (3 * (2 : ℝ) / 2 + 1) = ((3 : ℕ) : ℝ) + 1 := by norm_num
  have h2 : ((2 : ℝ) + 1) = ((2 : ℕ) : ℝ) + 1 := by norm_num
  rw [h20, h6, h1, h12, h10, h3, h2]
  rw [Real.Gamma_nat_eq_factorial 20, Real.Gamma_nat_eq_factorial 6, Real.Gamma_nat_eq_factorial 1]
  rw [Real.Gamma_nat_eq_factorial 12, Real.Gamma_nat_eq_factorial 10,
      Real.Gamma_nat_eq_factorial 3, Real.Gamma_nat_eq_factorial 2]
  norm_num; rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 48664320 := by
  unfold a; push_cast
  have h30 : (10 * (3 : ℝ) + 1) = ((30 : ℕ) : ℝ) + 1 := by norm_num
  have h9 : (3 * (3 : ℝ) + 1) = ((9 : ℕ) : ℝ) + 1 := by norm_num
  have h18 : (6 * (3 : ℝ) + 1) = ((18 : ℕ) : ℝ) + 1 := by norm_num
  have h15 : (5 * (3 : ℝ) + 1) = ((15 : ℕ) : ℝ) + 1 := by norm_num
  have h3 : ((3 : ℝ) + 1) = ((3 : ℕ) : ℝ) + 1 := by norm_num
  have h12 : (3 : ℝ) / 2 + 1 = 3 / 2 + 1 := by ring
  have h32 : 3 * (3 : ℝ) / 2 + 1 = 9 / 2 + 1 := by ring
  rw [h30, h9, h18, h15, h3, h12, h32]
  rw [Real.Gamma_nat_eq_factorial 30, Real.Gamma_nat_eq_factorial 9,
      Real.Gamma_nat_eq_factorial 18, Real.Gamma_nat_eq_factorial 15,
      Real.Gamma_nat_eq_factorial 3]
  rw [gamma_five_halves, gamma_eleven_halves]
  have hpi : √Real.pi ≠ 0 := by positivity
  have h_cancel : ((Nat.factorial 30 : ℝ) * (Nat.factorial 9 : ℝ) * ((3 / 4) * √Real.pi)) /
    ((Nat.factorial 18 : ℝ) * (Nat.factorial 15 : ℝ) * ((945 / 32) * √Real.pi) *
     (Nat.factorial 3 : ℝ)) = 48664320 := by
    have : ((Nat.factorial 30 : ℝ) * (Nat.factorial 9 : ℝ) * ((3 / 4) * √Real.pi)) /
        ((Nat.factorial 18 : ℝ) * (Nat.factorial 15 : ℝ) * ((945 / 32) * √Real.pi) *
         (Nat.factorial 3 : ℝ)) =
      (((Nat.factorial 30 : ℝ) * (Nat.factorial 9 : ℝ) * (3 / 4)) /
       ((Nat.factorial 18 : ℝ) * (Nat.factorial 15 : ℝ) * (945 / 32) * (Nat.factorial 3 : ℝ))) *
      (√Real.pi / √Real.pi) := by ring
    rw [this, div_self hpi, mul_one]
    norm_num
  rw [h_cancel]
  norm_num; rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 29966636700 := by
  unfold a; push_cast
  have h40 : (10 * (4 : ℝ) + 1) = ((40 : ℕ) : ℝ) + 1 := by norm_num
  have h12 : (3 * (4 : ℝ) + 1) = ((12 : ℕ) : ℝ) + 1 := by norm_num
  have h2 : ((4 : ℝ) / 2 + 1) = ((2 : ℕ) : ℝ) + 1 := by norm_num
  have h24 : (6 * (4 : ℝ) + 1) = ((24 : ℕ) : ℝ) + 1 := by norm_num
  have h20 : (5 * (4 : ℝ) + 1) = ((20 : ℕ) : ℝ) + 1 := by norm_num
  have h6 : (3 * (4 : ℝ) / 2 + 1) = ((6 : ℕ) : ℝ) + 1 := by norm_num
  have h4 : ((4 : ℝ) + 1) = ((4 : ℕ) : ℝ) + 1 := by norm_num
  rw [h40, h12, h2, h24, h20, h6, h4]
  rw [Real.Gamma_nat_eq_factorial 40, Real.Gamma_nat_eq_factorial 12, Real.Gamma_nat_eq_factorial 2]
  rw [Real.Gamma_nat_eq_factorial 24, Real.Gamma_nat_eq_factorial 20,
      Real.Gamma_nat_eq_factorial 6, Real.Gamma_nat_eq_factorial 4]
  norm_num; rfl

/--
Conjecture: the supercongruences $a(n p^r) \equiv a(n p^{r-1}) \pmod{p^{3r}}$ hold for all
primes $p \ge 5$ and all positive integers $n$ and $r$.
-/
@[category research open, AMS 11]
theorem supercongruence (p n r : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (hn : 1 ≤ n) (hr : 1 ≤ r) :
  a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] :=
by sorry

end OeisA364178
