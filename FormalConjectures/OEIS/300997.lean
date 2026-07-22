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

/-!
# Conjectures associated with A300997

A300997: $a(n)$ is the number of steps needed to reach a stable configuration in the 1D cellular
automaton initialized with one cell with mass $n$ and based on the rule "each cell gives half of
its mass, rounded down, to its right neighbor".
The stable configuration is $n$ cells with mass 1.

*References:*
- [A300997](https://oeis.org/A300997)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

namespace OeisA300997


open List Nat Function Set

/--
A300997: $a(n)$ is the number of steps needed to reach a stable configuration in the 1D cellular
automaton initialized with one cell with mass $n$ and based on the rule "each cell gives half of
its mass, rounded down, to its right neighbor".
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


@[category test, AMS 11]
lemma a_one : a 1 = 0 := by sorry

@[category test, AMS 11]
lemma a_two : a 2 = 1 := by sorry

@[category test, AMS 11]
lemma a_three : a 3 = 3 := by sorry

@[category test, AMS 11]
lemma a_four : a 4 = 4 := by sorry

@[category test, AMS 11]
lemma a_five : a 5 = 6 := by sorry


/--
A300997: $a(n)$ is the number of steps needed to reach a stable configuration in the 1D cellular
automaton initialized with one cell with mass $n$ and based on the rule "each cell gives half of
its mass, rounded down, to its right neighbor".
The stable configuration is $n$ cells with mass 1.

A formal proof has been found with the methods described in [arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/300997.wip.lean#L1153"]
theorem a_succ_eq : ∀ n : ℕ, 1 ≤ n → a (n + 1) = a n + 1 ∨ a (n + 1) = a n + 2 := by
    sorry

end OeisA300997
