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

open Nat Int Real

/--
The auxiliary sequence $b(k)$, where $b(1)=2$ and $b(k) = b(k-1) + \mathrm{lcm}(\lfloor \sqrt{2} \cdot k \rfloor, b(k-1))$ for $k \ge 2$.
-/
noncomputable def b : ℕ → ℕ
| 0 => 0 -- Placeholder for a 1-indexed sequence
| 1 => 2
| k + 1 => -- This computes b(k+1) based on b(k). The index is k+1 >= 2.
  let b_prev := b k
  let k_val : ℕ := k + 1
  -- Calculation of $\lfloor \sqrt{2} \cdot k_{val} \rfloor$, where k_val is the current index.
  let m_real := (Real.sqrt 2) * k_val.cast
  let m_int : ℤ := Int.floor m_real
  let m_nat : ℕ := m_int.toNat
  b_prev + b_prev.lcm m_nat


/--
A323386: $a(n) = b(n+1)/b(n) - 1$ where $b(k)$ is defined recursively.
-/
noncomputable def A323386 (n : ℕ) : ℕ :=
  match n with
  | 0 => 0 -- Sequence is 1-indexed.
  | n_idx =>
    let bn_plus_1 := b (n_idx + 1)
    let bn := b n_idx
    (bn_plus_1 / bn) - 1


theorem a_one : A323386 1 = 1 := by
  simp_all![ A323386]
  exact (.trans (by rw [ (by norm_num only[ ←not_lt,Int.floor_eq_iff,←lt_div_iff₀, and_self,Real.sqrt_lt]:⌊_⌋=2)]) (by decide) )

theorem a_two : A323386 2 = 1 := by
  norm_num [A323386]
  simp_all [b]
  norm_num[Int.toNat,show⌊√2*2⌋=2∧⌊√2*3⌋=4by norm_num[←not_lt,Int.floor_eq_iff,←lt_div_iff₀,Real.sqrt_lt]]

theorem a_three : A323386 3 = 5 := by
  norm_num[A323386]
  simp_all [b]
  norm_num[Int.toNat,show⌊√2*2⌋=2∧⌊√2*3⌋=4∧⌊√2*4⌋ = 5by norm_num[Int.floor_eq_iff,←not_lt,←lt_div_iff₀,Real.sqrt_lt]]

theorem a_four : A323386 4 = 7 := by
  norm_num[A323386]
  norm_num[b,id]
  norm_num[show⌊√2*2⌋=2∧⌊√2*3⌋=.sqrt (2 *9)by norm_num[Int.floor_eq_iff,←not_lt,←lt_div_iff₀,Real.sqrt_lt],Int.toNat, add_assoc]
  norm_num [((Int.floor_eq_iff.2 _) :_ = (2*16).sqrt), (Int.floor_eq_iff.2 @_:_=(2*25).sqrt), Real.le_sqrt _,←not_lt,Real.sqrt_lt _,←lt_div_iff₀]

/--
Conjecture 1: This sequence consists only of 1's and primes.
Conjecture 2: Every odd prime of the form $\lfloor \sqrt{2} \cdot m \rfloor$ is a term of this sequence.
Conjecture 3: At the first appearance of each prime of the form $\lfloor \sqrt{2} \cdot m \rfloor$, it is the next prime after the largest prime that has already appeared.
-/
theorem oeis_a323386_conjecture_1 : ∀ (n : ℕ), 1 ≤ n → (A323386 n = 1 ∨ Nat.Prime (A323386 n)) := by
  sorry
