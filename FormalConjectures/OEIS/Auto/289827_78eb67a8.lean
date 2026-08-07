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

/--
A289827: $a(n)$ is the largest $m \le n$ such that $\pi(m + n) = \pi(m) + \pi(n)$, where $\pi$ is the prime counting function $\text{A000720}$ ($\pi(0) = 0$).
-/
noncomputable def A289827 (n : ℕ) : ℕ :=
  Nat.findGreatest (fun m => Nat.primeCounting (m + n) = Nat.primeCounting m + Nat.primeCounting n) n

-- Note: Nat.primeCounting is mathematically $\pi$. The notation `π` is not
-- available by default via the simple `open scoped Nat.Prime` in this setup,
-- so we use the full name `Nat.primeCounting` for clarity and reliability.
-- In the proof development environment, the notation might be available, but
-- using the full name is safer for a standalone definition.

theorem a_one : A289827 1 = 0 := by
  -- The largest m <= 1 such that pi(m+1) = pi(m) + pi(1).
  -- m=1: pi(2) = 1, pi(1) + pi(1) = 0 + 0 = 0. 1 != 0.
  -- m=0: pi(1) = 0, pi(0) + pi(1) = 0 + 0 = 0. 0 = 0.
  -- max m is 0.
  sorry

theorem a_two : A289827 2 = 2 := by
  -- m=2: pi(4) = 2, pi(2) + pi(2) = 1 + 1 = 2. 2 = 2.
  -- max m is 2.
  sorry

theorem a_three : A289827 3 = 2 := by
  -- m=3: pi(6) = 3, pi(3) + pi(3) = 2 + 2 = 4. 3 != 4.
  -- m=2: pi(5) = 3, pi(2) + pi(3) = 1 + 2 = 3. 3 = 3.
  -- max m is 2.
  sorry

theorem a_four : A289827 4 = 4 := by
  -- m=4: pi(8) = 4, pi(4) + pi(4) = 2 + 2 = 4. 4 = 4.
  -- max m is 4.
  sorry

/--
First conjecture: for $n > 1$, all $a(n)$ belong to the set $\{1, 2, 4, 10\}$.
-/
theorem oeis_289827_conjecture_0 (n : ℕ) (hn : 1 < n) :
    A289827 n = 1 ∨ A289827 n = 2 ∨ A289827 n = 4 ∨ A289827 n = 10 := by
  sorry
