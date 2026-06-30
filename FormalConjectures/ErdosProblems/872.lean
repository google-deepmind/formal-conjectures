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

This file states Erdős Problem 872 for the primitive-set saturation game on $\{2, \dots, n\}$.
The game value `L n` is defined by a finite minimax recursion: Prolonger moves first and maximizes
the final size of the claimed primitive set, while Shortener minimizes it.

The problem statement does not fix the turn order. This file fixes Prolonger to move first,
following the convention used in the forum discussion of the problem. The choice is not cosmetic:
computational data suggests the Shortener-first value tracks $\pi(n)$ while the Prolonger-first
value grows linearly, and the questions below concern the Prolonger-first quantity.

*References:*
- [erdosproblems.com/872](https://www.erdosproblems.com/872)
- [erdosproblems.com/forum/thread/872](https://www.erdosproblems.com/forum/thread/872)
-/

open Filter

namespace Erdos872

noncomputable section

/-- A primitive subset of $\{2, \dots, n\}$ is a set in which no element divides another.
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

open scoped Classical in
/-- The legal moves from a position: unclaimed elements whose insertion preserves primitiveness. -/
def legalMoves {n : ℕ} (p : GamePos n) : Finset ℕ :=
  p.pool.filter fun x => IsPrimitive n (insert x p.claimed)

/-- Membership in `legalMoves`: a legal move is a pool element whose insertion preserves
primitiveness. -/
@[category API, AMS 5]
lemma mem_legalMoves {n : ℕ} {p : GamePos n} {x : ℕ} :
    x ∈ legalMoves p ↔ x ∈ p.pool ∧ IsPrimitive n (insert x p.claimed) := by
  classical
  simp [legalMoves]

/-- Apply a move by claiming `x` and removing it from the unclaimed pool.

This function is intentionally total: if `x` is not legal, it still returns the formal position
obtained by inserting and erasing `x`. The minimax recursion below only calls it for
`x ∈ legalMoves p`. -/
def applyMove {n : ℕ} (p : GamePos n) (x : ℕ) : GamePos n where
  claimed := insert x p.claimed
  pool := p.pool.erase x

/-- The empty starting position on $\{2, \dots, n\}$. -/
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

/-- Each move claims exactly one pool element, so the minimax value never exceeds the number of
already claimed elements plus the number of still unclaimed elements. -/
@[category API, AMS 5]
lemma gameValueAux_le {n : ℕ} (fuel : ℕ) (turn : Bool) (p : GamePos n) :
    gameValueAux fuel turn p ≤ p.claimed.card + p.pool.card := by
  induction fuel generalizing turn p with
  | zero =>
    simp only [gameValueAux]
    exact Nat.le_add_right _ _
  | succ fuel ih =>
    have key : ∀ x ∈ legalMoves p,
        gameValueAux fuel (!turn) (applyMove p x) ≤ p.claimed.card + p.pool.card := by
      intro x hx
      have hxpool : x ∈ p.pool := (mem_legalMoves.mp hx).1
      have h1 : (insert x p.claimed).card ≤ p.claimed.card + 1 := Finset.card_insert_le _ _
      have h2 : (p.pool.erase x).card = p.pool.card - 1 := Finset.card_erase_of_mem hxpool
      have h3 : 0 < p.pool.card := Finset.card_pos.mpr ⟨x, hxpool⟩
      have h4 : gameValueAux fuel (!turn) (applyMove p x) ≤
          (insert x p.claimed).card + (p.pool.erase x).card := ih (!turn) (applyMove p x)
      omega
    have key' : ∀ v ∈ (legalMoves p).image
        (fun x => gameValueAux fuel (!turn) (applyMove p x)),
        v ≤ p.claimed.card + p.pool.card := by
      intro v hv
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
      exact key x hx
    simp only [gameValueAux]
    split_ifs with h ht
    · exact Finset.max'_le _ _ _ key'
    · exact key' _ (Finset.min'_mem _ _)
    · exact Nat.le_add_right _ _

/-- The minimax value of the primitive-set saturation game from `p`, with Prolonger to move.

This is a genuine game-value definition rather than an uninterpreted placeholder. It unfolds the
finite game tree up to `p.pool.card` moves; at each node Prolonger maximizes and Shortener
minimizes the eventual terminal cardinality. -/
def gameLength {n : ℕ} : GamePos n → ℕ := fun p =>
  gameValueAux p.pool.card true p

/-- The Erdős primitive-set game length on $\{2, \dots, n\}$. -/
def L (n : ℕ) : ℕ := gameLength (startPos n)

/- ## Erdős Problem 872

The problem asks for asymptotic lower bounds on `L(n)`. Two specific targets are stated. -/

/-- Erdős Problem 872, part (i) (weak form): there exists a constant $\epsilon > 0$ such that the
game length is at least $\epsilon \cdot n$ for all sufficiently large $n$. -/
@[category research open, AMS 5 11 91]
theorem erdos_872.parts.i : answer(sorry) ↔
    ∃ ε > (0 : ℝ), ∀ᶠ n in atTop, (L n : ℝ) ≥ ε * n := by
  sorry

/-- Erdős Problem 872, part (ii) (strong form): for every $\epsilon > 0$, the game length is at
least $(1-\epsilon) \cdot n / 2$ for all sufficiently large $n$.

Status note: the forum thread (April-May 2026) records Shortener strategies giving
$L(n) \leq (23/48 + o(1)) \cdot n$ (described in the thread as accepted as correct, with a Lean
formalization in progress) and a claimed $L(n) \leq 0.19 \cdot n$, either of which would answer this
question negatively under the Prolonger-first convention. Neither is published, so the statement
is recorded here as the original Erdős question. -/
@[category research open, AMS 5 11 91]
theorem erdos_872.parts.ii : answer(sorry) ↔
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, (L n : ℝ) ≥ (1 - ε) * n / 2 := by
  sorry

/-- A trivial upper bound: a play can claim at most the $n - 1$ elements of $\{2, \dots, n\}$, so
$L(n) \leq n - 1$. -/
@[category textbook, AMS 5 11 91]
theorem erdos_872.trivial_upper_bound (n : ℕ) (hn : 2 ≤ n) :
    L n ≤ n - 1 := by
  calc L n ≤ (startPos n).claimed.card + (startPos n).pool.card :=
        gameValueAux_le (startPos n).pool.card true (startPos n)
    _ = n - 1 := by
        simp only [startPos, Finset.card_empty, Nat.card_Icc]
        omega

/-- Forum-related variant: how small can a maximal primitive subset of $\{2, \dots, n\}$ be?
The set of primes in $\{2, \dots, n\}$ is a maximal primitive subset of size $\pi(n)$, and the forum
thread asks whether this is the smallest possible for all $n \geq 2$. Equivalently: must every
completed play of the saturation game, by both players and regardless of strategy, claim at least
$\pi(n)$ elements? (Terminal positions of the game are exactly the maximal primitive subsets.) -/
@[category research open, AMS 5 11 91]
theorem erdos_872.variants.prime_question : answer(sorry) ↔
    ∀ n ≥ 2, ∀ A : Finset ℕ, Maximal (IsPrimitive n) A →
      ((Finset.Icc 2 n).filter Nat.Prime).card ≤ A.card := by
  sorry

end

end Erdos872
