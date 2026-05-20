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
A319524: $a(n)$ is the smallest number that belongs simultaneously to the two arithmetic progressions $\operatorname{prime}(n) + m \cdot \operatorname{prime}(n+1)$ and $\operatorname{prime}(n+1) + m' \cdot \operatorname{prime}(n+2)$, $m \ge 1, n \ge 1$.
Here, $\operatorname{prime}(k)$ denotes the $k$-th prime number, with $\operatorname{prime}(1)=2$.
-/
noncomputable def A319524 (n : ℕ) : ℕ :=
  let p (k : ℕ) : ℕ := Nat.nth Nat.Prime k
  -- The $k$-th prime (1-indexed) is p(k-1).
  -- However, note that in Lean's Nat.nth Nat.Prime, the sequence is 2, 3, 5, ...
  -- prime(n) is the n-th prime in OEIS, which is (n-1)-th in the 0-indexed mathlib list.
  let Pn    := p (n - 1) -- Safe since ℕ subtraction is capped at 0
  let Pnp1  := p n
  let Pnp2  := p (n + 1)

  sInf { x : ℕ |
    -- x belongs to the first progression: prime(n) + m*prime(n+1), m >= 1
    -- and x belongs to the second progression: prime(n+1) + m'*prime(n+2), m' >= 1
    ∃ (m m' : ℕ),
      1 ≤ m ∧ 1 ≤ m' ∧
      x = Pn + m * Pnp1 ∧
      x = Pnp1 + m' * Pnp2
  }

/--
Conjecture 1: There are infinitely many pairs of consecutive equal terms.
(Note that the first pair is (a(7), a(8)).)
-/
theorem oeis_a319524_conjecture_1 :
  Set.Infinite { n : ℕ | 1 ≤ n ∧ A319524 n = A319524 (n + 1) } :=
by sorry

/--
Conjecture 2: There exists no N such that the sequence is monotonic for n > N.
This is equivalent to saying the sequence is not eventually monotonic.
A sequence `a` is not eventually non-decreasing, AND not eventually non-increasing.
-/
theorem oeis_a319524_conjecture_2 :
  ¬ (∃ N : ℕ, (∀ n : ℕ, N < n → A319524 n ≤ A319524 (n + 1)) ∨ (∀ n : ℕ, N < n → A319524 n ≥ A319524 (n + 1))) :=
by sorry
