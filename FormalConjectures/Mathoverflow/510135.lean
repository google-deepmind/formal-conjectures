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

-- row count
def rc (n : ℕ) (board : Matrix (Fin n) (Fin n) ℕ) (i : Fin n) : ℕ :=
  ∑ j : Fin n, board i j

-- column count
def cc (n : ℕ) (board : Matrix (Fin n) (Fin n) ℕ) (i : Fin n) : ℕ :=
  ∑ j : Fin n, board j i

-- downward diagonal count
def ddc (n : ℕ) (board : Matrix (Fin n) (Fin n) ℕ) (k : Fin (2 * n - 1)) : ℕ :=
  ∑ i : Fin n, ∑ j : Fin n, (if i.1 + j.1 = k.1 then board i j else 0)

-- upward diagonal count
def udc (n : ℕ) (board : Matrix (Fin n) (Fin n) ℕ) (k : Fin (2 * n - 1)) : ℕ :=
  ∑ i : Fin n, ∑ j : Fin n,
    (if (i.1 : ℤ) - j.1 = (k.1 : ℤ) - (n - 1) then board i j else 0)

-- board count
def bc (n : ℕ) (board : Matrix (Fin n) (Fin n) ℕ) : ℕ :=
  ∑ i : Fin n, ∑ j : Fin n, board i j

def cells_ok_prop (n : ℕ) (board : Matrix (Fin n) (Fin n) ℕ) : Prop :=
  ∀ i j : Fin n, 0 ≤ board i j ∧ board i j ≤ 1

def rows_ok_prop (n c : ℕ) (board : Matrix (Fin n) (Fin n) ℕ) : Prop :=
  ∀ i : Fin n, rc n board i ≤ c

def cols_ok_prop (n c : ℕ) (board : Matrix (Fin n) (Fin n) ℕ) : Prop :=
  ∀ i : Fin n, cc n board i ≤ c

def dds_ok_prop (n c : ℕ) (board : Matrix (Fin n) (Fin n) ℕ) : Prop :=
  ∀ k : Fin (2 * n - 1), ddc n board k ≤ c

def uds_ok_prop (n c : ℕ) (board : Matrix (Fin n) (Fin n) ℕ) : Prop :=
  ∀ k : Fin (2 * n - 1), udc n board k ≤ c

def bc_ok_prop (n c : ℕ) (board : Matrix (Fin n) (Fin n) ℕ) : Prop :=
  bc n board = n * c

def n_c_placement_conjecture_prop (n c : ℕ) (board : Matrix (Fin n) (Fin n) ℕ) : Prop :=
  cells_ok_prop n board ∧
  rows_ok_prop n c board ∧
  cols_ok_prop n c board ∧
  dds_ok_prop n c board ∧
  uds_ok_prop n c board ∧
  bc_ok_prop n c board

/--
Can the coins placement problem be solved for every $n \ge 4$ and $0 \le c \le n$?
-/
@[category research open, AMS 5]
theorem n_c_coins_placement_conjecture : answer(sorry) ↔
  ∀ᵉ (n : ℕ) (c : ℕ) (hn : n ≥ 4) (hc : c ≤ n),
    ∃ board : Matrix (Fin n) (Fin n) ℕ,
    n_c_placement_conjecture_prop n c board := by
  sorry

/-
Let's check some solutions.
Note that I duplicate code to avoid `Decidable` issues.
-/

def cells_ok_bool (n : ℕ) (board : Matrix (Fin n) (Fin n) ℕ) : Bool :=
  decide (∀ i j : Fin n, 0 ≤ board i j ∧ board i j ≤ 1)

def rows_ok_bool (n c : ℕ) (board : Matrix (Fin n) (Fin n) ℕ) : Bool :=
  decide (∀ i : Fin n, rc n board i ≤ c)

def cols_ok_bool (n c : ℕ) (board : Matrix (Fin n) (Fin n) ℕ) : Bool :=
  decide (∀ i : Fin n, cc n board i ≤ c)

def dds_ok_bool (n c : ℕ) (board : Matrix (Fin n) (Fin n) ℕ) : Bool :=
  decide (∀ k : Fin (2 * n - 1), ddc n board k ≤ c)

def uds_ok_bool (n c : ℕ) (board : Matrix (Fin n) (Fin n) ℕ) : Bool :=
  decide (∀ k : Fin (2 * n - 1), udc n board k ≤ c)

def bc_ok_bool (n c : ℕ) (board : Matrix (Fin n) (Fin n) ℕ) : Bool :=
  decide (bc n board = n * c)

def n_c_placement_conjecture_bool (n c : ℕ) (board : Matrix (Fin n) (Fin n) ℕ) : Bool :=
  cells_ok_bool n board &&
  rows_ok_bool n c board &&
  cols_ok_bool n c board &&
  dds_ok_bool n c board &&
  uds_ok_bool n c board &&
  bc_ok_bool n c board

private def board_of_positions (positions : Finset (ℕ × ℕ)) : Matrix (Fin 8) (Fin 8) ℕ :=
  fun i j => if (i.1, j.1) ∈ positions then 1 else 0

/-

0  0  0  0  0  0  0  0
0  0  0  0  0  0  0  0
0  0  0  0  0  0  0  0
0  0  0  0  0  0  0  0
0  0  0  0  0  0  0  0
0  0  0  0  0  0  0  0
0  0  0  0  0  0  0  0
0  0  0  0  0  0  0  0

-/

private def _8_0_positions : Finset (ℕ × ℕ) := ∅

/-

0  1  0  0  0  0  0  0
0  0  0  1  0  0  0  0
0  0  0  0  0  1  0  0
0  0  0  0  0  0  0  1
0  0  1  0  0  0  0  0
1  0  0  0  0  0  0  0
0  0  0  0  0  0  1  0
0  0  0  0  1  0  0  0

-/

private def _8_1_positions : Finset (ℕ × ℕ) :=
  {(0, 1),
   (1, 3),
   (2, 5),
   (3, 7),
   (4, 2),
   (5, 0),
   (6, 6),
   (7, 4)}

/-

0  0  0  1  0  1  0  0
0  1  0  0  0  0  1  0
0  1  0  1  0  0  0  0
0  0  0  0  0  1  0  1
1  0  0  0  1  0  0  0
0  0  1  0  0  0  0  1
1  0  0  0  1  0  0  0
0  0  1  0  0  0  1  0

-/

private def _8_2_positions : Finset (ℕ × ℕ) :=
  {(0, 3), (0, 5),
   (1, 1), (1, 6),
   (2, 1), (2, 3),
   (3, 5), (3, 7),
   (4, 0), (4, 4),
   (5, 2), (5, 7),
   (6, 0), (6, 4),
   (7, 2), (7, 6)}

/-

0  0  1  1  1  0  0  0
0  0  0  0  1  1  1  0
1  0  1  0  0  0  0  1
1  0  0  1  0  0  0  1
0  1  0  1  0  0  1  0
0  1  0  0  0  1  1  0
0  0  1  0  0  1  0  1
1  1  0  0  1  0  0  0

-/

private def _8_3_positions : Finset (ℕ × ℕ) :=
  {(0, 2), (0, 3), (0, 4),
   (1, 4), (1, 5), (1, 6),
   (2, 0), (2, 2), (2, 7),
   (3, 0), (3, 3), (3, 7),
   (4, 1), (4, 3), (4, 6),
   (5, 1), (5, 5), (5, 6),
   (6, 2), (6, 5), (6, 7),
   (7, 0), (7, 1), (7, 4)}

/-

0  1  0  0  1  1  1  0
1  0  0  1  1  1  0  0
1  0  1  0  0  0  1  1
1  0  0  0  1  1  0  1
0  1  1  0  0  0  1  1
0  1  1  1  0  0  1  0
0  0  0  1  1  1  0  1
1  1  1  1  0  0  0  0

-/

private def _8_4_positions : Finset (ℕ × ℕ) :=
  {(0, 1), (0, 4), (0, 5), (0, 6),
   (1, 0), (1, 3), (1, 4), (1, 5),
   (2, 0), (2, 2), (2, 6), (2, 7),
   (3, 0), (3, 4), (3, 5), (3, 7),
   (4, 1), (4, 2), (4, 6), (4, 7),
   (5, 1), (5, 2), (5, 3), (5, 6),
   (6, 3), (6, 4), (6, 5), (6, 7),
   (7, 0), (7, 1), (7, 2), (7, 3)}

/-

1  0  1  0  1  1  1  0
1  1  0  1  0  1  1  0
1  0  1  1  1  0  0  1
1  0  1  0  0  1  1  1
1  1  0  1  1  0  0  1
0  1  0  1  0  1  1  1
0  1  1  0  1  1  0  1
0  1  1  1  1  0  1  0

-/

private def _8_5_positions : Finset (ℕ × ℕ) :=
  {(0, 0), (0, 2), (0, 4), (0, 5), (0, 6),
   (1, 0), (1, 1), (1, 3), (1, 5), (1, 6),
   (2, 0), (2, 2), (2, 3), (2, 4), (2, 7),
   (3, 0), (3, 2), (3, 5), (3, 6), (3, 7),
   (4, 0), (4, 1), (4, 3), (4, 4), (4, 7),
   (5, 1), (5, 3), (5, 5), (5, 6), (5, 7),
   (6, 1), (6, 2), (6, 4), (6, 5), (6, 7),
   (7, 1), (7, 2), (7, 3), (7, 4), (7, 6)}

/-

1  0  1  0  1  1  1  1
1  1  1  1  0  1  1  0
1  1  1  1  1  0  0  1
1  1  1  0  0  1  1  1
0  1  0  1  1  1  1  1
0  1  1  1  1  0  1  1
1  0  1  1  1  1  1  0
1  1  0  1  1  1  0  1

-/

 private def _8_6_positions : Finset (ℕ × ℕ) :=
   {(0, 0), (0, 2), (0, 4), (0, 5), (0, 6), (0, 7),
    (1, 0), (1, 1), (1, 2), (1, 3), (1, 5), (1, 6),
    (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 7),
    (3, 0), (3, 1), (3, 2), (3, 5), (3, 6), (3, 7),
    (4, 1), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7),
    (5, 1), (5, 2), (5, 3), (5, 4), (5, 6), (5, 7),
    (6, 0), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6),
    (7, 0), (7, 1), (7, 3), (7, 4), (7, 5), (7, 7)}

/-

0  1  1  1  1  1  1  1
1  1  1  1  1  1  1  0
1  1  1  1  0  1  1  1
1  1  0  1  1  1  1  1
1  1  1  1  1  1  0  1
1  1  1  1  1  0  1  1
1  0  1  1  1  1  1  1
1  1  1  0  1  1  1  1

-/

private def _8_7_positions : Finset (ℕ × ℕ) :=
  {(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7),
   (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6),
   (2, 0), (2, 1), (2, 2), (2, 3), (2, 5), (2, 6), (2, 7),
   (3, 0), (3, 1), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7),
   (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 7),
   (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 6), (5, 7),
   (6, 0), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7),
   (7, 0), (7, 1), (7, 2), (7, 4), (7, 5), (7, 6), (7, 7)}

/-

1  1  1  1  1  1  1  1
1  1  1  1  1  1  1  1
1  1  1  1  1  1  1  1
1  1  1  1  1  1  1  1
1  1  1  1  1  1  1  1
1  1  1  1  1  1  1  1
1  1  1  1  1  1  1  1
1  1  1  1  1  1  1  1
1  1  1  1  1  0  1  1
-/

private def _8_8_positions : Finset (ℕ × ℕ) :=
  {(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7),
   (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7),
   (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7),
   (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7),
   (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7),
   (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7),
   (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7),
   (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7 ,7)}

#eval n_c_placement_conjecture_bool 8 0 (board_of_positions _8_0_positions)

#eval n_c_placement_conjecture_bool 8 1 (board_of_positions _8_1_positions)

#eval n_c_placement_conjecture_bool 8 2 (board_of_positions _8_2_positions)

#eval n_c_placement_conjecture_bool 8 3 (board_of_positions _8_3_positions)

#eval n_c_placement_conjecture_bool 8 4 (board_of_positions _8_4_positions)

#eval n_c_placement_conjecture_bool 8 5 (board_of_positions _8_5_positions)

#eval n_c_placement_conjecture_bool 8 6 (board_of_positions _8_6_positions)

#eval n_c_placement_conjecture_bool 8 7 (board_of_positions _8_7_positions)

#eval n_c_placement_conjecture_bool 8 8 (board_of_positions _8_8_positions)

end Mathoverflow510135
