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
Coins on an `n × n` board, represented as a boolean matrix.
  `true`  indicates a  coin being present
  `false` indicates no coin being present
-/

def Board (n : ℕ) := Matrix (Fin n) (Fin n) Bool

namespace DuponcheelConjecture

variable {n : ℕ} (hn : n ≥ 4) {c : ℕ} (hc : c ≤ n)

/-- Transforms
a coin being present to 1
no coin being present to 0.
-/
def b2n (b : Bool) : ℕ := if b then 1 else 0

theorem n_m_coins_placement_conjecture (hn : n ≥ 4) (hc : c ≤ n) :
    ∃ (B : Board n),
      -- Each row, column, upward diagonal, and downward diagonal contains at most `c` coins.
      ∀ i : Fin n, ∑ j : Fin n, b2n (B i j) ≤ c ∧
      ∀ j : Fin n, ∑ i : Fin n, b2n (B i j) ≤ c ∧
      ∀ k : ℕ, ∑ i : Fin n, ∑ j : Fin n, (if (i : ℕ) + (j : ℕ) = k then b2n (B i j) else 0) ≤ c ∧
      ∀ k : ℤ, ∑ i : Fin n, ∑ j : Fin n, (if (i : ℤ) - (j : ℤ) = k then b2n (B i j) else 0) ≤ c ∧
      -- The total number of coins placed is `n * c`.
      ∑ i : Fin n, ∑ j : Fin n, b2n (B i j) = n * c

  := by sorry

end DuponcheelConjecture
