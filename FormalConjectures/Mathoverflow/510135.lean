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

*References:*
- [mathoverflow/510135](https://mathoverflow.net/questions/510135)
  asked by user [*Luc Duponcheel*](https://mathoverflow.net/users/513435/lucdupatstackexchange)
-/

namespace Mathoverflow510135

/--
Given $n \geq 4$ and $0 \leq c \leq n$,
it is always possible to place $n \cdot c$ coins on an $n \times n$ board such that
no row, column, upward diagonal, or downward diagonal
contains more than $c$ coins.
Each cell can hold at most $1$ coin.

This generalizes the traditional $n$-queens problem
(which corresponds to $c = 1$).

A board is encoded as a `Matrix (Fin n) (Fin n) ℕ`
  `1`  indicates a  coin being present
  `0` indicates no coin being present
-/
@[category research open, AMS 5]
theorem n_c_coins_placement_conjecture : answer(sorry) ↔
  ∀ᵉ (n : ℕ) (hn : n ≥ 4) (c : ℕ) (hc : c ≤ n),
    ∃ (board : Matrix (Fin n) (Fin n) ℕ),
      let rc (i : Fin n) :=
        ∑ j : Fin n, board i j
      let cc (i : Fin n) :=
        ∑ j : Fin n, board j i
      let ddc (k : ℕ) :=
        ∑ i : Fin n, ∑ j : Fin n, (if i + j = k then board i j else 0)
      let udc (k : ℤ) :=
        ∑ i : Fin n, ∑ j : Fin n, (if i - j = k then board i j else 0)
      let bc :=
        ∑ i : Fin n, ∑ j : Fin n, board i j
      -- Only zero or one coins at a position are allowed
      (∀ i j : Fin n, 0 ≤ board i j ∧ board i j ≤ 1) ∧
      -- Each row count is less than or equal to `c`
      (∀ i : Fin n, rc i ≤ c) ∧
      -- Each column count is less than or equal to `c`
      (∀ i : Fin n, cc i ≤ c) ∧
      -- Each downward diagonal count is less than or equal to `c`
      (∀ k : ℕ, ddc k ≤ c) ∧
      -- Each upward diagonal count is less than or equal to `c`
      (∀ k : ℤ, udc k ≤ c) ∧
      -- The board count is equal to `n * c`.
      bc = n * c
  := by
       sorry

end Mathoverflow510135

