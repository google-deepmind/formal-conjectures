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

module

public import FormalConjecturesUtil

/-!
# Generalized n-Queens Conjecture
# (replacing the traditional n-queens problem with a coin placement problem)

*References:*
- [mathoverflow/510135](https://mathoverflow.net/questions/510135)
  asked by user [*Luc Duponcheel*](https://mathoverflow.net/users/513435/lucdupatstackexchange)

- [A Generalization of the n-Queen Problem, by Le Maohua, Li Weixuan and Edward T. Wang](https://sysmath.cjoe.ac.cn/jssc/CN/PDF/44564#page=2) (1990)
-/

@[expose] public section

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
@[category research solved, AMS 5]
theorem n_c_coins_placement_conjecture : answer(True) ↔
  ∀ᵉ (n : ℕ) (c : ℕ) (hn : n ≥ 4) (hc : c ≤ n),
    ∃ board : Matrix (Fin n) (Fin n) ℕ,
    n_c_placement_conjecture_prop n c board := by
  sorry

end Mathoverflow510135
