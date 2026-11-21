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
# Difference between product of composite numbers and the next prime number where this is $>1$

The sequence is:

Take the product of all composite numbers $\le p_n$ where $p_n$ is the $n$-th prime ($0$-indexed here, $1$-indexed in OEIS).

Calculate the difference to the smallest prime number that is at least this product $+2$. This should be a positive number $\ge 2$.

This difference is $a(n)$.

*References:*
- [A249241](https://oeis.org/A249241)-/

@[expose] public section

namespace OeisA249241

/-- The smallest prime $\ge n$. -/
def nextPrime (n : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes n)

/--
The sequence $a_n = p - \frac{p_n !}{p_n \#}$, where $p_n$ is the $n$-th prime ($0$-indexed here, $1$-indexed in OEIS) and $p$ is the smallest prime with $p > \frac{p_n !}{p_n \#} + 1$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  letI frac := Nat.factorial (Nat.nth Nat.Prime n) / primorial (Nat.nth Nat.Prime n)
  nextPrime (frac + 2) - frac

@[category test, AMS 11]
theorem a_0 : a 0 = 2 := by
  simp [a]
  rw [Nat.le_antisymm_iff]
  constructor <;> simp [nextPrime]
  · use 3
    norm_num
  · intros
    omega

@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by
  simp [a]
  norm_num [show primorial 3 = 6 by rfl]
  rw [Nat.le_antisymm_iff]
  constructor <;> simp [nextPrime]
  · use 3
    norm_num
  · intros
    omega

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by
  simp [a]
  norm_num [show primorial 5 = 30 by rfl]
  suffices nextPrime 6 = 7 by lia
  rw [Nat.le_antisymm_iff]
  constructor <;> simp [nextPrime]
  · use 7
    norm_num
  · intro m _ _
    rw [show m = 6 by omega]
    norm_num

/-- Conjecture: All terms of A249241 are prime. -/
@[category research open, AMS 11]
theorem conjecture : ∀ n, Nat.Prime (a n) := by
  sorry

end OeisA249241
