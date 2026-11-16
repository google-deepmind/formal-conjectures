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
# Number of primes between $n^3 - n$ and $n^3$

For $n \ge 1$, $a(n)$ is the number of primes $p$ satisfying $n^3 - n < p \le n^3$,
given by $\pi(n^3) - \pi(n^3 - n)$.

*References:*
- [A216265](https://oeis.org/A216265)
-/

@[expose] public section

namespace OeisA216265

/-- Number of primes between $n^3 - n$ and $n^3$. -/
def a (n : ℕ) : ℕ :=
  Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by
  have hp : ∀ {k : ℕ}, (k + 1).Prime →
      Nat.primeCounting (k + 1) = Nat.primeCounting k + 1 := fun {k} h => by
    rw [← Nat.primesLE_card_eq_primeCounting, ← Nat.primesLE_card_eq_primeCounting,
      Nat.primesLE_succ, if_pos h, Finset.card_insert_of_notMem (Nat.notMem_primesLE k)]
  have hn : ∀ {k : ℕ}, ¬ (k + 1).Prime →
      Nat.primeCounting (k + 1) = Nat.primeCounting k := fun {k} h => by
    rw [← Nat.primesLE_card_eq_primeCounting, ← Nat.primesLE_card_eq_primeCounting,
      Nat.primesLE_succ, if_neg h]
  rw [a, show 4 ^ 3 - 4 = 60 by norm_num, show 4 ^ 3 = 63 + 1 by norm_num]
  rw [hn (by norm_num : ¬ (63 + 1).Prime)]
  rw [show (63 : ℕ) = 62 + 1 from rfl, hn (by norm_num)]
  rw [show (62 : ℕ) = 61 + 1 from rfl, hn (by norm_num)]
  rw [show (61 : ℕ) = 60 + 1 from rfl, hp (by norm_num)]
  omega

@[category test, AMS 11]
theorem a_5 : a 5 = 0 := by
  have hn : ∀ {k : ℕ}, ¬ (k + 1).Prime →
      Nat.primeCounting (k + 1) = Nat.primeCounting k := fun {k} h => by
    rw [← Nat.primesLE_card_eq_primeCounting, ← Nat.primesLE_card_eq_primeCounting,
      Nat.primesLE_succ, if_neg h]
  rw [a, show 5 ^ 3 - 5 = 120 by norm_num, show 5 ^ 3 = 124 + 1 by norm_num]
  rw [hn (by norm_num : ¬ (124 + 1).Prime)]
  rw [show (124 : ℕ) = 123 + 1 from rfl, hn (by norm_num)]
  rw [show (123 : ℕ) = 122 + 1 from rfl, hn (by norm_num)]
  rw [show (122 : ℕ) = 121 + 1 from rfl, hn (by norm_num)]
  rw [show (121 : ℕ) = 120 + 1 from rfl, hn (by norm_num)]
  omega

@[category test, AMS 11]
theorem a_10 : a 10 = 2 := by
  have hp : ∀ {k : ℕ}, (k + 1).Prime →
      Nat.primeCounting (k + 1) = Nat.primeCounting k + 1 := fun {k} h => by
    rw [← Nat.primesLE_card_eq_primeCounting, ← Nat.primesLE_card_eq_primeCounting,
      Nat.primesLE_succ, if_pos h, Finset.card_insert_of_notMem (Nat.notMem_primesLE k)]
  have hn : ∀ {k : ℕ}, ¬ (k + 1).Prime →
      Nat.primeCounting (k + 1) = Nat.primeCounting k := fun {k} h => by
    rw [← Nat.primesLE_card_eq_primeCounting, ← Nat.primesLE_card_eq_primeCounting,
      Nat.primesLE_succ, if_neg h]
  rw [a, show 10 ^ 3 - 10 = 990 by norm_num, show 10 ^ 3 = 999 + 1 by norm_num]
  rw [hn (by norm_num : ¬ (999 + 1).Prime)]
  rw [show (999 : ℕ) = 998 + 1 from rfl, hn (by norm_num)]
  rw [show (998 : ℕ) = 997 + 1 from rfl, hn (by norm_num)]
  rw [show (997 : ℕ) = 996 + 1 from rfl, hp (by norm_num)]
  rw [show (996 : ℕ) = 995 + 1 from rfl, hn (by norm_num)]
  rw [show (995 : ℕ) = 994 + 1 from rfl, hn (by norm_num)]
  rw [show (994 : ℕ) = 993 + 1 from rfl, hn (by norm_num)]
  rw [show (993 : ℕ) = 992 + 1 from rfl, hn (by norm_num)]
  rw [show (992 : ℕ) = 991 + 1 from rfl, hn (by norm_num)]
  rw [show (991 : ℕ) = 990 + 1 from rfl, hp (by norm_num)]
  omega

/--
Conjecture: For every $n > 13$, $a(n) > 0$.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 13 < n) : 0 < a n := by
  sorry

end OeisA216265
