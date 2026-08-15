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

open Matrix Nat Int

/--
A226163: Determinant of the $(p_n-1)/2$-by-$(p_n-1)/2$ matrix with $(i,j)$-entry being the Legendre symbol
$$\left(\frac{i^2 - \left(\frac{p_n-1}{2}\right)! \cdot j}{p_n}\right)$$
where $p_n$ is the $n$-th prime.
The sequence is naturally indexed starting from $n=2$.
-/
noncomputable def A226163 (n : ℕ) : ℤ :=
  if h : n < 2 then 0 else

  -- p is the n-th prime, p_n. Mathlib's nth Nat.Prime is 0-indexed, so we use (n-1).
  -- Since n >= 2, p >= 3 is an an odd prime.
  let p : ℕ := Nat.nth Nat.Prime (n - 1)

  -- Matrix dimension m = (p-1)/2.
  let m : ℕ := (p - 1) / 2

  -- The constant C = ((p-1)/2)! as an integer.
  let C : ℤ := m.factorial.cast

  -- The matrix M has entries in ℤ.
  let M : Matrix (Fin m) (Fin m) ℤ := fun i j =>
    -- 1-based indices i' and j' for the formula: 1 <= i', j' <= m.
    let i' : ℤ := (i.val + 1).cast
    let j' : ℤ := (j.val + 1).cast

    -- Argument for the Legendre symbol: i'^2 - C * j'
    let arg : ℤ := i' * i' - C * j'

    -- jacobiSym is the Legendre symbol since p is prime.
    jacobiSym arg p

  M.det

theorem a_two : A226163 2 = 0 := by
  sorry

theorem a_three : A226163 3 = -1 := by
  sorry

theorem a_four : A226163 4 = 0 := by
  sorry

theorem a_five : A226163 5 = 0 := by
  sorry

/--
Conjecture: a(n) = 0 if and only if p_n ≡ 3 (mod 4).
-/
theorem oeis_226163_conjecture_0 (n : ℕ) (h_n : 2 ≤ n) :
    A226163 n = 0 ↔ Nat.nth Nat.Prime (n - 1) % 4 = 3 := by
  sorry
