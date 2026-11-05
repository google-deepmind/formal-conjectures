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
# Number of primes between $n^2$ and $n^2 + (\log_2 n)^2$

For $n \ge 1$, $a(n)$ is the number of primes between $n^2$ and $n^2 + (\log_2 n)^2$ inclusive,
given by $\pi(\lfloor n^2 + (\log_2 n)^2 \rfloor) - \pi(n^2)$.

*References:*
- [A217317](https://oeis.org/A217317)
-/

@[expose] public section

namespace OeisA217317

/-- Number of primes between $n^2$ and $n^2 + (\log_2 n)^2$ inclusive. -/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let upperBound : ℕ := Int.toNat ⌊(n : ℝ) ^ 2 + (Real.logb 2 n) ^ 2⌋
    Nat.primeCounting upperBound - Nat.primeCounting (n ^ 2)

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by
  simp [a]

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  have h : Real.logb 2 2 = 1 := Real.logb_self_eq_one (by norm_num)
  have h2 : Int.toNat ⌊(2 : ℝ) ^ 2 + (1 : ℝ) ^ 2⌋ = 5 := by norm_num; rfl
  unfold a
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte, Nat.cast_ofNat, h, h2]
  decide

@[category test, AMS 11]
theorem a_4 : a 4 = 2 := by
  have h : Real.logb 2 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    norm_num
  have h2 : Int.toNat ⌊(4 : ℝ) ^ 2 + (2 : ℝ) ^ 2⌋ = 20 := by norm_num; rfl
  unfold a
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte, Nat.cast_ofNat, h, h2]
  decide

@[category test, AMS 11]
theorem a_8 : a 8 = 3 := by
  have h : Real.logb 2 8 = 3 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    norm_num
  have h2 : Int.toNat ⌊(8 : ℝ) ^ 2 + (3 : ℝ) ^ 2⌋ = 73 := by norm_num; rfl
  unfold a
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte, Nat.cast_ofNat, h, h2]
  decide

@[category test, AMS 11]
theorem a_16 : a 16 = 4 := by
  have h : Real.logb 2 16 = 4 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    norm_num
  have h2 : Int.toNat ⌊(16 : ℝ) ^ 2 + (4 : ℝ) ^ 2⌋ = 272 := by norm_num; rfl
  have hp : ∀ {k : ℕ}, (k + 1).Prime →
      Nat.primeCounting (k + 1) = Nat.primeCounting k + 1 := fun {k} hk => by
    rw [← Nat.primesLE_card_eq_primeCounting, ← Nat.primesLE_card_eq_primeCounting,
      Nat.primesLE_succ, if_pos hk, Finset.card_insert_of_notMem (Nat.notMem_primesLE k)]
  have hn : ∀ {k : ℕ}, ¬ (k + 1).Prime →
      Nat.primeCounting (k + 1) = Nat.primeCounting k := fun {k} hk => by
    rw [← Nat.primesLE_card_eq_primeCounting, ← Nat.primesLE_card_eq_primeCounting,
      Nat.primesLE_succ, if_neg hk]
  unfold a
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte, Nat.cast_ofNat, h, h2]
  rw [show (16 ^ 2 : ℕ) = 256 by norm_num, show (272 : ℕ) = 271 + 1 from rfl]
  rw [hn (by norm_num : ¬ (271 + 1).Prime)]
  rw [show (271 : ℕ) = 270 + 1 from rfl, hp (by norm_num)]
  rw [show (270 : ℕ) = 269 + 1 from rfl, hn (by norm_num)]
  rw [show (269 : ℕ) = 268 + 1 from rfl, hp (by norm_num)]
  rw [show (268 : ℕ) = 267 + 1 from rfl, hn (by norm_num)]
  rw [show (267 : ℕ) = 266 + 1 from rfl, hn (by norm_num)]
  rw [show (266 : ℕ) = 265 + 1 from rfl, hn (by norm_num)]
  rw [show (265 : ℕ) = 264 + 1 from rfl, hn (by norm_num)]
  rw [show (264 : ℕ) = 263 + 1 from rfl, hn (by norm_num)]
  rw [show (263 : ℕ) = 262 + 1 from rfl, hp (by norm_num)]
  rw [show (262 : ℕ) = 261 + 1 from rfl, hn (by norm_num)]
  rw [show (261 : ℕ) = 260 + 1 from rfl, hn (by norm_num)]
  rw [show (260 : ℕ) = 259 + 1 from rfl, hn (by norm_num)]
  rw [show (259 : ℕ) = 258 + 1 from rfl, hn (by norm_num)]
  rw [show (258 : ℕ) = 257 + 1 from rfl, hn (by norm_num)]
  rw [show (257 : ℕ) = 256 + 1 from rfl, hp (by norm_num)]
  omega

/--
Conjecture: For every $n > 4765516$, $a(n) > 0$.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 4765516 < n) : 0 < a n := by
  sorry

end OeisA217317
