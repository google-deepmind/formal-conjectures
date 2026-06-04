/-
Copyright 2025 The Formal Conjectures Authors.

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

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.Basic

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
-/

/--
Coins on an `n × n` board, represented as a boolean matrix.
  `true`  indicates a  coin being present
  `false` indicates no coin being present
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.Basic

namespace DuponcheelConjecture

abbrev BoolBoard (n : ℕ) := Matrix (Fin n) (Fin n) Bool

abbrev NatBoard (n : ℕ) := Matrix (Fin n) (Fin n) ℕ

theorem n_c_coins_placement_conjecture {n c : ℕ} (hn : n ≥ 4) (hc : c ≤ n) :
    ∃ (B : BoolBoard n),
      let N := B.map (fun b ↦ if b then 1 else 0) ;
      -- Each row, column, upward diagonal, and downward diagonal
      -- contains at most `c` coins.
      ∀ i : Fin n, ∑ j : Fin n, N i j ≤ c ∧
      ∀ j : Fin n, ∑ i : Fin n, N i j ≤ c ∧
      ∀ k : ℕ, ∑ i : Fin n, ∑ j : Fin n, (if i + j = k then N i j else 0) ≤ c ∧
      ∀ k : ℤ, ∑ i : Fin n, ∑ j : Fin n, (if i - j = k then N i j else 0) ≤ c ∧
      -- Total number of coins placed is `n * c`.
      ∑ i : Fin n, ∑ j : Fin n, N i j = n * c

  := by sorry


end DuponcheelConjecture

