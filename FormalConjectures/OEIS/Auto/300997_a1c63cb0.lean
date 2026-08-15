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

open List Nat Function Set

/--
A300997: $a(n)$ is the number of steps needed to reach a stable configuration in the 1D cellular automaton initialized with one cell with mass $n$ and based on the rule "each cell gives half of its mass, rounded down, to its right neighbor".
The stable configuration is $n$ cells with mass 1.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let half_ceil (m : ℕ) : ℕ := (m + 1) / 2
  let half_floor (m : ℕ) : ℕ := m / 2

  let trim_trailing_zeros (l : List ℕ) : List ℕ :=
    (List.reverse l).dropWhile (fun x => x = 0) |>.reverse

  let ca_step (config : List ℕ) : List ℕ :=
    let base_masses := config.map half_ceil ++ [0]
    let received_masses := 0 :: config.map half_floor

    let next_config_long := List.zipWith Nat.add base_masses received_masses

    trim_trailing_zeros next_config_long

  if n = 0 then
    0
  else
    let initial_config : List ℕ := [n]
    let target_config : List ℕ := List.replicate n 1

    -- State after t steps, computed by folding ca_step t times using foldl over a range.
    let S (t : ℕ) : List ℕ := (List.range t).foldl (fun acc _ => ca_step acc) initial_config

    -- The set of time steps k at which the configuration is stable.
    let stable_steps : Set ℕ := {k | S k = target_config}

    -- a(n) is the smallest k in this set, defined by the set infimum (sInf).
    sInf stable_steps


theorem a_one : a 1 = 0 := by sorry
theorem a_two : a 2 = 1 := by sorry
theorem a_three : a 3 = 3 := by sorry
theorem a_four : a 4 = 4 := by sorry


/--
Conjecture A300997: The finite difference of this sequence only contains 1's and 2's.
Specifically, $\forall n \ge 1, a(n+1) - a(n) \in \{1, 2\}$.
It is also conjectured that $a(n) = 2n - \sum_{k=1}^{n} I(k)$ where $I(n)$ is the indicator function of some other sequence (A305992).
-/
theorem oeis_a300997_finite_difference_is_one_or_two :
  ∀ n : ℕ, 1 ≤ n → a (n + 1) = a n + 1 ∨ a (n + 1) = a n + 2 := by sorry
