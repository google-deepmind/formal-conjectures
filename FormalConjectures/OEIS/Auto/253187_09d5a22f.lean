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

open Nat Finset

/--
The $x$-th pentagonal number, $\frac{x(3x-1)}{2}$, for $x \ge 0$.
-/
private def pentagonal_first (x : ℕ) : ℕ := (x * (3 * x - 1)) / 2

/--
The $y$-th "second pentagonal number", $\frac{y(3y+1)}{2}$, for $y \ge 0$.
-/
private def pentagonal_second (y : ℕ) : ℕ := (y * (3 * y + 1)) / 2

/--
The generalized decagonal number $m(4m-3)$ is calculated implicitly here.
The number of $\mathbb{Z}$ indices $m$ such that $m(4m-3)=r$. This is 1 if $r$ is a
generalized decagonal number (i.e., $16r+9$ is a perfect square), and 0 otherwise.
-/
private def count_generalized_decagonal_index (r : ℕ) : ℕ :=
  if Nat.sqrt (16 * r + 9) * Nat.sqrt (16 * r + 9) = 16 * r + 9 then 1 else 0

/--
A253187: Number of ordered ways to write $n$ as the sum of a pentagonal number, a second pentagonal number and a generalized decagonal number.
$$a(n) = \# \{ (x, y, m) \in \mathbb{N} \times \mathbb{N} \times \mathbb{Z} \mid n = \frac{x(3x-1)}{2} + \frac{y(3y+1)}{2} + m(4m-3) \}$$
-/
def A253187 (n : ℕ) : ℕ :=
  -- Iterate x and y up to n, which is a sufficient bound.
  (range (n + 1)).sum fun x =>
    (range (n + 1)).sum fun y =>
      let sum_pent := pentagonal_first x + pentagonal_second y
      if sum_pent <= n then
        count_generalized_decagonal_index (n - sum_pent)
      else
        0


theorem a_zero : A253187 0 = 1 := by
  sorry

theorem a_one : A253187 1 = 2 := by
  sorry

theorem a_two : A253187 2 = 2 := by
  sorry

theorem a_three : A253187 3 = 2 := by
  sorry


-- Generalized polygonal number formula, $\frac{(k-2)z^2 - (k-4)z}{2}$, for $z \in \mathbb{Z}$.
def polygonal_num_val (k : ℕ) (z : ℤ) : ℤ :=
  if k ≥ 3 then
    let k' : ℤ := k
    -- The numerator is always even when k >= 3, so division is exact integer division.
    ((k' - 2) * z * z - (k' - 4) * z) / 2
  else 0

-- The k-gonal number (first type), index $x \in \mathbb{N}$.
-- Since $x \ge 0$ and $k \ge 3$, the result of polygonal_num_val is $\ge 0$.
def P_k_first (k : ℕ) (x : ℕ) : ℕ :=
  (polygonal_num_val k (x : ℤ)).toNat

-- The second k-gonal number, index $y \in \mathbb{N}$.
-- For $y \in \mathbb{N}$ and $k \ge 3$, $P_k(-(y:\mathbb{Z}))$ is always non-negative.
def P_k_second (k : ℕ) (y : ℕ) : ℕ :=
  (polygonal_num_val k (-(y : ℤ))).toNat

-- The set of pairs (k,m) in the conjecture.
private noncomputable def C_pairs : Set (ℕ × ℕ) :=
  {(5, 7), (5, 9), (5, 13), (6, 5), (6, 7), (7, 5)}

/--
A253187 Conjecture: a(n) > 0 for all n. Also, for any ordered pair (k,m) among (5,7), (5,9), (5,13), (6,5), (6,7), (7,5), each nonnegative integer n can be written as the sum of a k-gonal number, a second k-gonal number and a generalized m-gonal number.
-/
theorem A253187.universal_sum_conjecture :
  (∀ n : ℕ, A253187 n > 0) ∧
  ∀ k m, (k, m) ∈ C_pairs →
    ∀ n : ℕ, ∃ x y : ℕ, ∃ z : ℤ,
      (P_k_first k x) + (P_k_second k y) + (polygonal_num_val m z).toNat = n := by sorry
