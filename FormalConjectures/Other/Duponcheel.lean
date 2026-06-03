import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.Basic

open BigOperators

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
A configuration of coins on an `n × n` board, represented as a boolean matrix.
`true` indicates a coin is present; `false` indicates an empty cell.
-/
def BoardConfiguration (n : ℕ) := Matrix (Fin n) (Fin n) Bool

namespace DuponcheelConjecture

variable {n : ℕ} (hn : n ≥ 4) {c : ℕ} (hc : c ≤ n)

/-- Helper to count a coin as 1 and an empty cell as 0. -/
def coinValue (b : Bool) : ℕ := if b then 1 else 0

/-- The total number of coins placed on the board is exactly `n * c`. -/
def HasTotalCoins (B : BoardConfiguration n) (c : ℕ) : Prop :=
  ∑ i : Fin n, ∑ j : Fin n, coinValue (B i j) = n * c

/-- Every row contains at most `c` coins. -/
def RowCondition (B : BoardConfiguration n) (c : ℕ) : Prop :=
  ∀ i : Fin n, ∑ j : Fin n, coinValue (B i j) ≤ c

/-- Every column contains at most `c` coins. -/
def ColCondition (B : BoardConfiguration n) (c : ℕ) : Prop :=
  ∀ j : Fin n, ∑ i : Fin n, coinValue (B i j) ≤ c

/-- Every 45-degree upward diagonal contains at most `c` coins.
    Upward diagonals are characterized by lines where `i + j = k`. -/
def UpDiagCondition (B : BoardConfiguration n) (c : ℕ) : Prop :=
  ∀ k : ℕ, ∑ i : Fin n, ∑ j : Fin n,
    (if (i : ℕ) + (j : ℕ) = k
     then coinValue (B i j)
     else 0) ≤ c

/-- Every 45-degree downward diagonal contains at most `c` coins.
    Downward diagonals are characterized by lines where `i - j = k`
    (using integers to avoid underflow). -/
def DownDiagCondition (B : BoardConfiguration n) (c : ℕ) : Prop :=
  ∀ k : ℤ, ∑ i : Fin n, ∑ j : Fin n,
    (if (i : ℤ) - (j : ℤ) = k
     then coinValue (B i j)
     else 0) ≤ c

/--
The main conjecture statement:
For any valid `n` and `c`, there exists a valid board configuration.
-/
theorem generalized_n_queens_conjecture (hn : n ≥ 4) (hc : c ≤ n) :
    answer(sorry) ↔ ∃ (B : BoardConfiguration n),
      HasTotalCoins B c ∧
      RowCondition B c ∧
      ColCondition B c ∧
      UpDiagCondition B c ∧
      DownDiagCondition B c := by
  sorry

end DuponcheelConjecture
