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
A214497: Smallest $k \ge 0$ such that $(3^n-k)2^n-1$ and $(3^n-k)2^n+1$ are a twin prime pair.
-/
noncomputable def A214497 (n : ℕ) : ℕ :=
  -- Nat.sInf is the rigorous definition of the minimum element of a set of natural numbers,
  -- which translates "smallest k" directly.
  sInf {k : ℕ | Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)}

theorem a_one : A214497 1 = 0 := by
  sorry

theorem a_two : A214497 2 = 6 := by
  sorry

theorem a_three : A214497 3 = 3 := by
  sorry

theorem a_four : A214497 4 = 9 := by
  sorry


/--
OEIS A214497 Conjecture: there is always one such k for each n>0.
That is, for every $n>0$, there exists a $k \ge 0$ such that
$(3^n-k)2^n-1$ and $(3^n-k)2^n+1$ are a twin prime pair.
-/
theorem oeis_214497_conjecture_0 (n : ℕ) (hn : n > 0) :
    ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1) := by
  sorry
