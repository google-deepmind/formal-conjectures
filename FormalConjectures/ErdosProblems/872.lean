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
# Erdős Problem 872

This file states Erdős Problem 872 for the primitive-set saturation game on `{2, ..., n}`.
The game value `L n` is defined by a finite minimax recursion: Prolonger moves first and maximizes
the final size of the claimed primitive set, while Shortener minimizes it.

*References:*
- [erdosproblems.com/872](https://www.erdosproblems.com/872)
- [erdosproblems.com/forum/thread/872](https://www.erdosproblems.com/forum/thread/872)
-/

open Filter

namespace Erdos872

noncomputable section

/-- A primitive subset of `{2, ..., n}` is a set in which no element divides another.
The quantified divisibility condition is one-sided because the variables range over all ordered
pairs of distinct elements. -/
def IsPrimitive (n : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 2 n ∧ ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ a ∣ b

/- The two-player primitive-set saturation game on `{2, ..., n}`.

A position records the already claimed set and the unclaimed pool. A legal move chooses `x` from
the pool such that adding `x` keeps the claimed set primitive. The next position inserts `x` into
the claimed set and erases `x` from the pool. Elements that have become illegal are left in the
pool, but `legalMoves` filters them out at the next turn. Thus the game ends exactly when no
unclaimed element can be legally added, and the pool cardinality strictly decreases after every
played move.
-/

/-- A game position consists of the already claimed set and the still unclaimed pool. -/
structure GamePos (n : ℕ) where
  claimed : Finset ℕ
  pool : Finset ℕ

/-- The legal moves from a position: unclaimed elements whose insertion preserves primitiveness. -/
def legalMoves {n : ℕ} (p : GamePos n) : Finset ℕ := by
  classical
  exact p.pool.filter fun x => IsPrimitive n (insert x p.claimed)

/-- Apply a move by claiming `x` and removing it from the unclaimed pool.

This function is intentionally total: if `x` is not legal, it still returns the formal position obtained
by inserting and erasing `x`. The minimax recursion below only calls it for `x ∈ legalMoves p`. -/
def applyMove {n : ℕ} (p : GamePos n) (x : ℕ) : GamePos n where
  claimed := insert x p.claimed
  pool := p.pool.erase x

/-- The empty starting position on `{2, ..., n}`. -/
def startPos (n : ℕ) : GamePos n where
  claimed := ∅
  pool := Finset.Icc 2 n

/-- Auxiliary finite minimax recursion with an explicit fuel bound.

At a Prolonger turn (`turn = true`) the recursion takes the maximum over legal moves; at a
Shortener turn (`turn = false`) it takes the minimum. If there are no legal moves, or the fuel is
exhausted, it returns the current final size `p.claimed.card`. Starting with fuel `p.pool.card` is
sufficient because every played move erases the chosen pool element. -/
def gameValueAux {n : ℕ} : ℕ → Bool → GamePos n → ℕ
  | 0, _turn, p => p.claimed.card
  | fuel + 1, turn, p =>
      let moves := legalMoves p
      let f := fun x => gameValueAux fuel (!turn) (applyMove p x)
      let vals := moves.image f
      if h : moves.Nonempty then
        let hvals : vals.Nonempty := h.image f
        if turn then vals.max' hvals else vals.min' hvals
      else
        p.claimed.card

/-- The minimax value of the primitive-set saturation game from `p`, with Prolonger to move.

This is a genuine game-value definition rather than an uninterpreted placeholder. It unfolds the
finite game tree up to `p.pool.card` moves; at each node Prolonger maximizes and Shortener
minimizes the eventual terminal cardinality. -/
def gameLength {n : ℕ} : GamePos n → ℕ := fun p =>
  gameValueAux p.pool.card true p

/-- The Erdős-Cameron primitive-set game length on `{2, ..., n}`. -/
def L (n : ℕ) : ℕ := gameLength (startPos n)

/- ## Erdős Problem 872

The problem asks for asymptotic lower bounds on `L(n)`. Two specific targets are stated. -/

/-- Erdős Problem 872, weak form: there exists a constant `ε > 0` such that the game length is at
least `ε * n` for all sufficiently large `n`. -/
@[category research open, AMS 5 11 91]
theorem erdos_872.parts.weak : answer(sorry) ↔
    ∃ ε > (0 : ℝ), ∀ᶠ n in atTop, (L n : ℝ) ≥ ε * n := by
  sorry

/-- Erdős Problem 872, strong form: for every `ε > 0`, the game length is at least
`(1 - ε) * n / 2` for all sufficiently large `n`. -/
@[category research open, AMS 5 11 91]
theorem erdos_872.parts.strong : answer(sorry) ↔
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, (L n : ℝ) ≥ (1 - ε) * n / 2 := by
  sorry

/-- A trivial upper bound: a play can claim at most the elements of `{2, ..., n}`, so
`L(n) ≤ n - 1`. -/
@[category research solved, AMS 5 11 91]
theorem erdos_872.trivial_upper_bound (n : ℕ) (hn : 2 ≤ n) :
    L n ≤ n - 1 := by
  sorry

/-- Forum-related variant (Angelo): is the game length always at least `π(n)`? The forum thread
notes that the set of primes is a maximal primitive subset of `{2, ..., n}` and asks whether this
is the smallest possible size of a maximal primitive subset. -/
@[category research open, AMS 5 11 91]
theorem erdos_872.variants.prime_question : answer(sorry) ↔
    ∀ n ≥ 2, L n ≥ ((Finset.Icc 2 n).filter Nat.Prime).card := by
  sorry

/-- Buddhdev conditional variant: a private manuscript shared with the contributor; statement
records the conditional implication as stated by the author, pending publication. Under the
restricted safe-edge hypothesis for T2-strategy-generated finite graph and residual slot-hypergraph
states, the manuscript states a lower bound of order
`n * (log log n)^2 / log n`. -/
@[category research open, AMS 5 11 91]
theorem erdos_872.variants.buddhdev_conditional : answer(sorry) ↔
    ∃ c > (0 : ℝ), ∀ᶠ n in atTop,
      (L n : ℝ) ≥ c * n * (Real.log (Real.log n))^2 / Real.log n := by
  sorry

end

end Erdos872
