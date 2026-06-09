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
# Duponcheel's Generalized n-Queens Conjecture
# (replacing the traditional n-queens problem with a coin placement problem)

Given `n ≥ 4` and `0 ≤ c ≤ n`,
it is always possible to place `n * c` coins on an `n × n` board such that
no row, column, upward diagonal, or downward diagonal
contains more than `c` coins.
Each cell can hold at most 1 coin.

This generalizes the traditional n-queens problem
(which corresponds to `c = 1`).

Coins on an `n × n` board, represented as a boolean matrix.
  `true`  indicates a  coin being present
  `false` indicates no coin being present
-/

namespace DuponcheelConjecture

variable {n : ℕ} (hn : n ≥ 4) {c : ℕ} (hc : c ≤ n)

/--
Below is the theorem
-/
@[category research open, AMS 5]
theorem n_c_coins_placement_conjecture : answer(sorry) ↔
    ∃ (BoolBoard : Matrix (Fin n) (Fin n) Bool),
      let NatBoard : Matrix (Fin n) (Fin n) ℕ :=
        BoolBoard.map (fun b ↦ if b then 1 else 0)
      let rc (i : Fin n) :=
        ∑ j : Fin n, NatBoard i j
      let cc (i : Fin n) :=
        ∑ j : Fin n, NatBoard j i
      let ddc (k : ℕ) :=
        ∑ i : Fin n, ∑ j : Fin n, (if i + j = k then NatBoard i j else 0)
      let udc (k : ℤ) :=
        ∑ i : Fin n, ∑ j : Fin n, (if i - j = k then NatBoard i j else 0)
      let bc :=
        ∑ i : Fin n, ∑ j : Fin n, NatBoard i j
      -- Each row count is less than or equal to `c`
      ∀ i : Fin n, rc i ≤ c ∧
      -- Each column count is less than or equal to `c`
      ∀ i : Fin n, cc i ≤ c ∧
      -- Each downward diagonal count is less than or equal to `c`
      ∀ k : ℕ, ddc k ≤ c ∧
      -- Each upward diagonal count is less than or equal to `c`
      ∀ k : ℤ, udc k ≤ c ∧
      -- The board count is equal to `n * c`.
      bc = n * c
  := by sorry

end DuponcheelConjecture

