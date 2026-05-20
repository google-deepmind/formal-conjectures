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
A264025: Number of ways to write $n$ as $x^2 + y(2y+1) + \frac{z(z+1)}{2}$
where $x, y$ and $z$ are nonnegative integers with $z$ or $z+1$ prime.
-/
noncomputable def A264025 (n : ℕ) : ℕ :=
  Nat.card { p : ℕ × ℕ × ℕ //
    let (x, y, z) := p
    x ^ 2 + y * (2 * y + 1) + z * (z + 1) / 2 = n ∧
    (Nat.Prime z ∨ Nat.Prime (z + 1))
  }

/-- The set of indices n for which A264025 n = 1, according to the conjecture. -/
def A264025_singletons : Finset ℕ :=
  {1, 2, 3, 8, 9, 23, 30, 44, 48, 198, 219, 1344}

/--
A264025 Conjecture: (i) a(n) > 0 for all n > 0, and a(n) = 1 only for n = 1, 2, 3, 8, 9, 23, 30, 44, 48, 198, 219, 1344.
-/
theorem oeis_264025_conjecture_0 :
  (∀ n : ℕ, n > 0 → A264025 n > 0)
  ∧ (∀ n : ℕ, A264025 n = 1 ↔ n ∈ A264025_singletons) :=
by sorry
