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

open Nat Set

/--
A321576: $a(n)$ is the smallest $b > 1$ such that $b^n - (b-1)^n$ has all divisors $d \equiv 1 \pmod n$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h_n : n > 0 then
    let S_n : Set ℕ :=
      { b | b > 1 ∧
          let k := b ^ n - (b - 1) ^ n -- Note: This is natural number subtraction. For n > 1 and b >= 2, b^n > (b-1)^n.
          ∀ (d : ℕ), d ∣ k → d ≡ 1 [MOD n] }
    -- sInf finds the smallest element of a set in a partial order, which is the minimum for $\mathbb{N}$.
    sInf S_n
  else
    0

-- Keeping the structure of the provided snippet but marking proofs as sorry
theorem a_one : a 1 = 2 := by sorry
theorem a_two : a 2 = 2 := by sorry
theorem a_three : a 3 = 2 := by sorry
theorem a_four : a 4 = 3 := by sorry

/--
oeis_321576_conjecture_1: Sequence continues for n = 56..95 (unconfirmed terms marked with a '?'):
20301625?, 171, 30, 2, ?, 2, 156, 18298, 405825?, 442, 361285?, 2, 8365, 553, 392106?, 2, ?, 2, 75, 4975?,
31351?, 1914, 247339?, 2, ?, 1513?, 42, 2, ?, 391, 87, 406?, ?, 2, ?, 39, ?, 63, 142, 145
-/
theorem oeis_321576_conjecture_1 : a 57 = 171 ∧ a 59 = 2 ∧ a 95 = 145 := by
  sorry

/--
Conjecture: If n is prime, then a(n) = 2. Conjecture: If n is composite, then a(n) > 2.
Equivalently, for $n > 1$, $a(n)=2$ if and only if $n$ is prime.
-/
theorem oeis_321576_conjecture_prime_iff_val_two (n : ℕ) (h_n : n > 1) :
  a n = 2 ↔ Nat.Prime n :=
by sorry
