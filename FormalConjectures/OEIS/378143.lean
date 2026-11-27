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
# Smallest primes of the form $(2p)^{2^n} + 1$

$a(n)$ is the smallest prime of the form $(2p)^{2^n} + 1$ for some prime $p$.

*References:*
- [A378143](https://oeis.org/A378143)
-/
open Nat Set

namespace OeisA378143

/--
The smallest prime of the form $(2p)^{2^n} + 1$ for some prime $p$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { k : ℕ | k.Prime ∧ ∃ p : ℕ, p.Prime ∧ k = (2 * p) ^ (2 ^ n) + 1 }

@[category API, AMS 11]
lemma a_val {n : ℕ} {k : ℕ} (hk_prime : k.Prime) (hk_eq : k = 4 ^ (2 ^ n) + 1) : a n = k := by
  unfold a
  have h_mem : k ∈ { k : ℕ | k.Prime ∧ ∃ p : ℕ, p.Prime ∧ k = (2 * p) ^ (2 ^ n) + 1 } := by
    refine ⟨hk_prime, 2, by norm_num, ?_⟩
    exact hk_eq
  have h_bounds :
      ∀ x ∈ { k : ℕ | k.Prime ∧ ∃ p : ℕ, p.Prime ∧ k = (2 * p) ^ (2 ^ n) + 1 }, k ≤ x := by
    rintro x ⟨hx_prime, p, hp_prime, hx_eq⟩
    have hp : 2 ≤ p := hp_prime.two_le
    have h1 : 4 ≤ 2 * p := by omega
    have h2 : 4 ^ (2 ^ n) ≤ (2 * p) ^ (2 ^ n) := Nat.pow_le_pow_left h1 (2 ^ n)
    have h3 : 4 ^ (2 ^ n) + 1 ≤ (2 * p) ^ (2 ^ n) + 1 := Nat.add_le_add_right h2 1
    rw [← hk_eq, ← hx_eq] at h3
    exact h3
  exact IsLeast.csInf_eq ⟨h_mem, h_bounds⟩

@[category test, AMS 11]
theorem a_0 : a 0 = 5 := a_val (by norm_num) (by norm_num)
@[category test, AMS 11]
theorem a_1 : a 1 = 17 := a_val (by norm_num) (by norm_num)
@[category test, AMS 11]
theorem a_2 : a 2 = 257 := a_val (by norm_num) (by norm_num)
@[category test, AMS 11]
theorem a_3 : a 3 = 65537 := a_val (by norm_num) (by norm_num)
@[category test, AMS 11]
theorem a_4 : a 4 = 808551180810136214718004658177 := by
  sorry

/--
The last digit of each value of $a(n)$, where $n \ge 1$, is 7.
-/
@[category research open, AMS 11]
theorem conjecture_1 : ∀ (n : ℕ), 1 ≤ n → a n % 10 = 7 := by
  sorry

/--
If $10^{2^n} + 1$ is prime, then either $4^{2^n} + 1$ or $6^{2^n} + 1$ is prime.
-/
@[category research open, AMS 11]
theorem conjecture_2 :
  ∀ (n : ℕ),
    Nat.Prime (10 ^ (2 ^ n) + 1) →
      Nat.Prime (4 ^ (2 ^ n) + 1) ∨ Nat.Prime (6 ^ (2 ^ n) + 1) :=
  by sorry

end OeisA378143
