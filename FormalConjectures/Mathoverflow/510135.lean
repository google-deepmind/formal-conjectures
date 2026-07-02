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

def satisfies_placement_conjecture_bool (n c : ℕ) (board : Matrix (Fin n) (Fin n) ℕ) : Bool :=
  let rc (i : Fin n) :=
    ∑ j : Fin n, board i j
  let cc (i : Fin n) :=
    ∑ j : Fin n, board j i
  let ddc (k : Fin (2 * n - 1)) :=
    ∑ i : Fin n, ∑ j : Fin n, (if i.1 + j.1 = k.1 then board i j else 0)
  let udc (k : Fin (2 * n - 1)) :=
    ∑ i : Fin n, ∑ j : Fin n,
      (if (i.1 : ℤ) - j.1 = (k.1 : ℤ) - (n - 1) then board i j else 0)
  let bc :=
    ∑ i : Fin n, ∑ j : Fin n, board i j
  let cells_ok : Bool :=
    decide (∀ i j : Fin n, 0 ≤ board i j ∧ board i j ≤ 1)
  let rows_ok : Bool :=
    decide (∀ i : Fin n, rc i ≤ c)
  let cols_ok : Bool :=
    decide (∀ i : Fin n, cc i ≤ c)
  let dds_ok : Bool :=
    decide (∀ k : Fin (2 * n - 1), ddc k ≤ c)
  let uds_ok : Bool :=
    decide (∀ k : Fin (2 * n - 1), udc k ≤ c)
  let count_ok : Bool :=
    decide (bc = n * c)
  cells_ok && rows_ok && cols_ok && dds_ok && uds_ok && count_ok

def satisfies_placement_conjecture (n c : ℕ) (board : Matrix (Fin n) (Fin n) ℕ) : Prop :=
  satisfies_placement_conjecture_bool n c board = true

/--
Can every such placement problem be solved for every $n \ge 4$ and $0 \le c \le n$?
-/
@[category research open, AMS 5]
theorem n_c_coins_placement_conjecture : answer(sorry) ↔
  ∀ᵉ (n : ℕ) (c : ℕ) (hn : n ≥ 4) (hc : c ≤ n),
    ∃ board : Matrix (Fin n) (Fin n) ℕ, satisfies_placement_conjecture n c board := by
  sorry

/--
Let's check some boards satifying the conjecture.
-/

private def board_of_positions (positions : Finset (ℕ × ℕ)) : Matrix (Fin 8) (Fin 8) ℕ :=
  fun i j => if (i.1, j.1) ∈ positions then 1 else 0

private def _8_1_positions : Finset (ℕ × ℕ) :=
  {(0, 1),
   (1, 3),
   (2, 5),
   (3, 7),
   (4, 2),
   (5, 0),
   (6, 6),
   (7, 4)}

private def _8_2_positions : Finset (ℕ × ℕ) :=
  {(0, 3), (0, 5),
   (1, 1), (1, 6),
   (2, 1), (2, 3),
   (3, 5), (3, 7),
   (4, 0), (4, 4),
   (5, 2), (5, 7),
   (6, 0), (6, 4),
   (7, 2), (7, 6)}

private def _8_3_positions : Finset (ℕ × ℕ) :=
  {(0, 2), (0, 3), (0, 4),
   (1, 4), (1, 5), (1, 6),
   (2, 0), (2, 2), (2, 7),
   (3, 0), (3, 3), (3, 7),
   (4, 1), (4, 3), (4, 6),
   (5, 1), (5, 5), (5, 6),
   (6, 2), (6, 5), (6, 7),
   (7, 0), (7, 1), (7, 4)}

private def _8_4_positions : Finset (ℕ × ℕ) :=
  {(0, 1), (0, 4), (0, 5), (0, 6),
   (1, 0), (1, 3), (1, 4), (1, 5),
   (2, 0), (2, 2), (2, 6), (2, 7),
   (3, 0), (3, 4), (3, 5), (3, 7),
   (4, 1), (4, 2), (4, 6), (4, 7),
   (5, 1), (5, 2), (5, 3), (5, 6),
   (6, 3), (6, 4), (6, 5), (6, 7),
   (7, 0), (7, 1), (7, 2), (7, 3)}

private def _8_5_positions : Finset (ℕ × ℕ) :=
  {(0, 0), (0, 2), (0, 4), (0, 5), (0, 6),
   (1, 0), (1, 1), (1, 3), (1, 5), (1, 6),
   (2, 0), (2, 2), (2, 3), (2, 4), (2, 7),
   (3, 0), (3, 2), (3, 5), (3, 6), (3, 7),
   (4, 0), (4, 1), (4, 3), (4, 4), (4, 7),
   (5, 1), (5, 3), (5, 5), (5, 6), (5, 7),
   (6, 1), (6, 2), (6, 4), (6, 5), (6, 7),
   (7, 1), (7, 2), (7, 3), (7, 4), (7, 6)}

 private def _8_6_positions : Finset (ℕ × ℕ) :=
  {(0, 0), (0, 2), (0, 4), (0, 5), (0, 6), (0, 7),
   (1, 0), (1, 1), (1, 2), (1, 3), (1, 5), (1, 6),
   (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 7),
   (3, 0), (3, 1), (3, 2), (3, 5), (3, 6), (3, 7),
   (4, 1), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7),
   (5, 1), (5, 2), (5, 3), (5, 4), (5, 6), (5, 7),
   (6, 0), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6),
   (7, 0), (7, 1), (7, 3), (7, 4), (7, 5), (7, 7)}

private def _8_7_positions : Finset (ℕ × ℕ) :=
  {(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7),
   (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6),
    (2, 0), (2, 1), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7),
    (3, 0), (3, 1), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7),
    (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 7),
    (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 6), (5, 7),
    (6, 0), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7),
    (7, 0), (7, 1), (7, 2), (7, 4), (7, 5), (7, 6), (7, 7)}

#eval satisfies_placement_conjecture_bool 8 1 (board_of_positions _8_1_positions)
#eval satisfies_placement_conjecture_bool 8 2 (board_of_positions _8_2_positions)
#eval satisfies_placement_conjecture_bool 8 3 (board_of_positions _8_3_positions)
#eval satisfies_placement_conjecture_bool 8 4 (board_of_positions _8_4_positions)
#eval satisfies_placement_conjecture_bool 8 5 (board_of_positions _8_5_positions)
#eval satisfies_placement_conjecture_bool 8 6 (board_of_positions _8_6_positions)
#eval satisfies_placement_conjecture_bool 8 7 (board_of_positions _8_7_positions)

end Mathoverflow510135

