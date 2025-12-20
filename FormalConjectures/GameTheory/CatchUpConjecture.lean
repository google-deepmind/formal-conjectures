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

import FormalConjectures.Util.ProblemImports

/-!
# The Catch-Up game and conjecture

The game **Catch-Up** (Isaksen–Ismail–Brams–Nealen, 2015) is a two-player, perfect-information game
played on a finite nonempty set `S` of positive integers. Each time a player removes a number from
`S`, that number is added to the player’s score.

**Rules.**
* The scores start at `0`. Player `P1` starts by removing **exactly one** number from `S`.
* After the first move, players alternate turns. On a turn, the current player removes **one or more**
  numbers from `S`, one at a time, and must keep removing numbers until their score becomes
  **at least** the opponent’s score; before the final pick they must remain **strictly behind**.
* If the current player cannot catch up (in particular, even taking all remaining numbers would still
  leave them behind), the game ends immediately: the current player receives all remaining numbers.

When `S` is empty, the player with higher score wins; equal scores give a draw.

In this file we define:
* `Player` and `Outcome`,
* the recursive evaluator `value` (optimal play),
* `catchUpValueN` for the initial segment `{1, …, N}`,
* the conjecture `catchUp_draw_when_T_even`.

## Example
For `S = {1,2,3,4}` one play is: `P1` takes `2`, `P2` takes `1` then `4`, and `P1` takes `3`,
ending with scores `(5,5)`.

## References
A. Isaksen, M. Ismail, S. J. Brams, A. Nealen,
*Catch-Up: A Game in Which the Lead Alternates,* Game & Puzzle Design 1(2), 38–49 (2015).

Category and AMS classification:
--------------------------------
This is a research-level open problem in combinatorial game theory and number theory.

-/


namespace CatchUp

noncomputable section
open scoped BigOperators

/-
Define Player type for the Catch-Up game.
-/
inductive Player | P1 | P2
deriving DecidableEq, Repr

def Player.other : Player → Player
| P1 => P2
| P2 => P1

/-
Define Outcome type, negation, ordering, and bestOutcome helper.
-/
inductive Outcome | Win | Loss | Draw
deriving DecidableEq, Repr

def Outcome.neg : Outcome → Outcome
| Win => Loss
| Loss => Win
| Draw => Draw

def Outcome.toInt : Outcome → ℤ
| Win => 1
| Draw => 0
| Loss => -1

instance : LE Outcome where
  le a b := a.toInt ≤ b.toInt

instance : LT Outcome where
  lt a b := a.toInt < b.toInt

instance : DecidableRel (· ≤ · : Outcome → Outcome → Prop) :=
  fun a b => inferInstanceAs (Decidable (a.toInt ≤ b.toInt))

instance : DecidableRel (· < · : Outcome → Outcome → Prop) :=
  fun a b => inferInstanceAs (Decidable (a.toInt < b.toInt))

def bestOutcome (os : List Outcome) : Outcome :=
  os.foldl (fun acc o => if acc < o then o else acc) Outcome.Loss

/-
Define the recursive game value function `value`.
-/
noncomputable def value (remaining : Finset ℕ) (s_me s_opp : ℕ) (isFirstMove : Bool) : Outcome :=
  if h : remaining = ∅ then
    if s_me > s_opp then Outcome.Win
    else if s_opp > s_me then Outcome.Loss
    else Outcome.Draw
  else
    if s_me + remaining.sum (fun x => x) < s_opp then
      Outcome.Loss
    else
      let moves := remaining.attach.toList
      let outcomes := moves.map (fun ⟨x, hx⟩ =>
        let s_me' := s_me + x
        let remaining' := remaining.erase x
        if isFirstMove then
          (value remaining' s_opp s_me' false).neg
        else
          if s_me' ≥ s_opp then
            (value remaining' s_opp s_me' false).neg
          else
            value remaining' s_me' s_opp false
      )
      bestOutcome outcomes
termination_by remaining.card
decreasing_by
  classical
  all_goals
    simpa [remaining'] using Finset.card_erase_lt_of_mem hx


/-
Define helper functions for the Catch-Up game on {1, ..., N}.
-/
def initialSet (N : ℕ) : Finset ℕ :=
  Finset.Icc 1 N

noncomputable def catchUpValueN (N : ℕ) : Outcome :=
  value (initialSet N) 0 0 true

def T (N : ℕ) : ℕ := N * (N + 1) / 2

/-- English version:
Let \(T_N = \sum_{k=1}^{N} k = \frac{N(N+1)}{2}\).
If \(T_N\) is even (equivalently \(N \equiv 0 \pmod 4\) or \(N \equiv 3 \pmod 4\)),
then under optimal play the game `Catch-Up(\(\{1, \ldots, N\}\))` ends in a draw.
-/

@[category research open, AMS 91 11]
theorem catchUp_draw_when_T_even (N : ℕ)
    (h_even : Even (T N)) :
    catchUpValueN N = Outcome.Draw := by
  sorry

end -- noncomputable section
end CatchUp
