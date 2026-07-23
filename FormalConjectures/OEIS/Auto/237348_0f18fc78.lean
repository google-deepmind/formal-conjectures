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
The $k$-th prime number, $p_k$, with $p_1=2$. This is $\operatorname{prime}(k)$ from the OEIS description.
-/
noncomputable def prime_k_1indexed (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/--
A237348: Number of ordered ways to write $n = k + m$ with $k > 0$ and $m > 0$ such that $\mathrm{prime}(k) + 4$ and $\mathrm{prime}(\mathrm{prime}(m)) + 4$ are both prime.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- The sum is over $k$ such that $1 \le k \le n - 1$.
  -- This range ensures $k > 0$ and $m = n - k > 0$.
  Finset.sum (Ico 1 n) fun k =>
    let m := n - k

    let pk := prime_k_1indexed k
    let cond1 : Prop := Nat.Prime (pk + 4)

    let pm_index := prime_k_1indexed m
    let ppm := prime_k_1indexed pm_index

    let cond2 : Prop := Nat.Prime (ppm + 4)

    if cond1 ∧ cond2 then 1 else 0


theorem a_one : a 1 = 0 := by
  sorry

theorem a_two : a 2 = 0 := by
  sorry

theorem a_three : a 3 = 1 := by
  sorry

theorem a_four : a 4 = 0 := by
  sorry


/--
A generalization of A237348 to a general even number $2d$.
The number of ordered ways to write $n = k + m$ with $k > 0$ and $m > 0$ such that
$\mathrm{prime}(k) + 2d$ and $\mathrm{prime}(\mathrm{prime}(m)) + 2d$ are both prime.
-/
noncomputable def a_generalized (n d : ℕ) : ℕ :=
  Finset.sum (Ico 1 n) fun k =>
    let m := n - k

    let pk := prime_k_1indexed k
    let cond1 : Prop := Nat.Prime (pk + 2 * d)

    let pm_index := prime_k_1indexed m
    let ppm := prime_k_1indexed pm_index

    let cond2 : Prop := Nat.Prime (ppm + 2 * d)

    if cond1 ∧ cond2 then 1 else 0

/--
OEIS A237348 Conjecture: For each $d = 1, 2, 3, \dots$ there is a positive integer $N(d)$
for which any integer $n > N(d)$ can be written as $k + m$ with $k > 0$ and $m > 0$ such that
$\mathrm{prime}(k) + 2d$ and $\mathrm{prime}(\mathrm{prime}(m)) + 2d$ are both prime.
-/
theorem oeis_237348_conjecture_0 :
  ∀ (d : ℕ), 1 ≤ d →
    ∃ (N : ℕ), 0 < N ∧
      ∀ (n : ℕ), N < n →
        0 < a_generalized n d := by sorry
