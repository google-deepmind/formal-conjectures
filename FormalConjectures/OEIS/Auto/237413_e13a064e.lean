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

open Nat

/--
A237413: Number of ways to write $n = k + m$ with $k > 0$ and $m > 0$ such that $p(k)^2 - 2$, $p(m)^2 - 2$ and $p(p(m))^2 - 2$ are all prime, where $p(j)$ denotes the $j$-th prime.
-/
noncomputable def A237413 (n : ℕ) : ℕ :=
  -- The j-th prime $p(j)$ is Nat.nth Nat.Prime (j-1).
  let p_j (j : ℕ) : ℕ := Nat.nth Nat.Prime (j - 1)

  -- The number of ways is the sum of the indicator function over $k \in \{1, 2, \dots, n-1\}$.
  (Finset.Ico 1 n).sum fun k ↦
    let m := n - k

    let pk := p_j k
    let pm := p_j m

    -- The argument for $p(p(m))$ is $p(m)$. Since $p(m) \ge 2$, this is a valid index $\ge 1$.
    -- To use $p_j$, we need to ensure $p_m \ge 1$. $p(m)$ is a prime, so $p(m) \ge 2 > 0$.
    let ppm := p_j pm

    -- All three expressions must be prime. The conversion of Prop to 0/1 handles the counting.
    if (pk ^ 2 - 2).Prime ∧ (pm ^ 2 - 2).Prime ∧ (ppm ^ 2 - 2).Prime then 1 else 0


theorem a_one : A237413 1 = 0 := by
  -- The Finset.Ico 1 1 is empty.
  simp only [A237413, Finset.Ico_self, Finset.sum_empty]

-- The a_two, a_three, a_four proofs from the prompt are incomplete and should be simplified/removed unless they are simple sanity checks.
-- I will keep them but ensure they are just placeholders since the focus is the conjecture.

theorem a_two : A237413 2 = 1 := by sorry

theorem a_three : A237413 3 = 2 := by sorry

theorem a_four : A237413 4 = 2 := by sorry

/--
Conjecture: $a(n) > 0$ for all $n > 1$.
-/
theorem oeis_237413_conjecture_0 (n : ℕ) : 1 < n → A237413 n > 0 := by
  sorry
