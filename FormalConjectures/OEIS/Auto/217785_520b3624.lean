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

open scoped Nat.Prime
open Set Polynomial

/--
A217785: Smallest integer $s>n$ such that $1+2s+3s^2+...+n s^{n-1}$ is prime.
The sum is $P_n(s) = \sum_{k=1}^n k s^{k-1} = \sum_{k=0}^{n-1} (k+1) s^k$.
-/
noncomputable def A217785 (n : ℕ) : ℕ :=
  let P_n (s : ℕ) : ℕ := Finset.sum (Finset.range n) fun k => (k + 1) * s ^ k
  let S : Set ℕ := {s | n < s ∧ Nat.Prime (P_n s)}
  sInf S


theorem a_two : A217785 2 = 3 := by sorry
theorem a_three : A217785 3 = 12 := by sorry
theorem a_four : A217785 4 = 12 := by sorry
theorem a_five : A217785 5 = 9 := by sorry

-- Definition of the polynomial $s_n(x) = \sum_{k=0}^n (k+1)x^k$ over ℤ[X]
noncomputable def s_poly (n : ℕ) : Polynomial ℤ :=
  Finset.sum (Finset.range (n + 1)) fun k => C (k + 1 : ℤ) * X ^ k

/--
oeis_217785_conjecture_1: This is related to the following conjecture of the author: The polynomials
$s_n(x)=\sum_{k=0}^n(k+1)x^k$ (for $n=1,2,3,\dots$) are all irreducible over the field of rational numbers;
moreover, $s_n(x)$ is reducible modulo every prime if and only if $n$ has the form $8k(k+1)$,
where $k$ is a positive integer.
-/
theorem oeis_217785_conjecture_1 :
  -- Part 1: Irreducibility over ℚ for all $n \ge 1$.
  (∀ (n : ℕ), 1 ≤ n → Irreducible (map (Int.castRingHom ℚ) (s_poly n)))
  ∧
  -- Part 2: Reducibility modulo every prime p iff n has the form 8k(k+1) for k > 0.
  (∀ (n : ℕ), 1 ≤ n →
    ( (∀ (p : ℕ), Nat.Prime p → ¬ Irreducible (map (Int.castRingHom (ZMod p)) (s_poly n)))
      ↔
      (∃ (k : ℕ), 0 < k ∧ n = 8 * k * (k + 1))
    )
  ) :=
by sorry
