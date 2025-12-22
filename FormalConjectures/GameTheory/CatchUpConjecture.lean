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
* The scores start at `0`. Player `p1` starts by removing **exactly one** number from `S`.
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
* the conjecture `value_of_even_mul_succ_self_div_two`.

## Example
For `S = {1,2,3,4}` one play is: `p1` takes `2`, `p2` takes `1` then `4`, and `p1` takes `3`,
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
inductive Player | p1 | p2
deriving DecidableEq, Repr

def Player.other : Player → Player
| p1 => p2
| p2 => p1

/-
Define Outcome type, negation, ordering, and bestOutcome helper.
-/
inductive Outcome | win | loss | draw
deriving DecidableEq, Repr

def Outcome.neg : Outcome → Outcome
| win => loss
| loss => win
| draw => draw

/--
Computes the best outcome for the current player from a list of possible outcomes.
Win > Draw > Loss.
-/
def Outcome.best (os : List Outcome) : Outcome :=
  os.foldl (fun
    | .win,  _     => .win
    | _,     .win  => .win
    | .draw, _     => .draw
    | _,     .draw => .draw
    | _,     _     => .loss) .loss


/-
Define the recursive game value functions.
-/

/-
`value remaining s_me s_opp isFirstMove` evaluates the position where:

* `remaining` is the set `S'` of numbers not yet taken.
* `s_me` is the current score of the player who is about to act (the “current player”).
* `s_opp` is the opponent’s current score.
* `isFirstMove` indicates whether we are in the special very first move of the whole game,
  where the rules force exactly one pick and then the turn passes.

The result is the game-theoretic value from the current player’s point of view:
`.win` / `.loss` / `.draw`, assuming optimal play from both sides.

We model a single *turn* (which may consist of several picks `$x_1,...,x_k$`) by recursion:
the current player chooses one number `x`; if they are still strictly behind after taking it, they must
continue the same turn (so the recursive call keeps the same “current player”);
once they catch up (score ≥ opponent), the turn ends and we swap players.
-/
noncomputable def valueAux (remaining : Finset ℕ) (s_me s_opp : ℕ) (isFirstMove : Bool) : Outcome :=
  -- If no numbers remain, the game is over. Compare final scores.
  if h : remaining = ∅ then
    if s_me > s_opp then
      -- Current player ends with strictly larger score.
      Outcome.win
    else if s_opp > s_me then
      -- Opponent ends with strictly larger score.
      Outcome.loss
    else
      -- Scores are equal.
      Outcome.draw
  else
    -- Terminal rule / pruning:
    -- If even taking *all* remaining numbers would still leave the current player behind,
    -- then there is no legal catch-up sequence (in the TeX: no `$x_1,...,x_k$` with final sum ≥ gap).
    -- By the rules, the current player takes everything and the game ends immediately,
    -- but under this inequality they must still lose.
    if s_me + remaining.sum (fun x => x) < s_opp then
      Outcome.loss
    else
      -- Otherwise, the current player can pick some `$x \in$ remaining`.
      -- We evaluate every possible next pick under optimal play, then take the best outcome.
      let moves := remaining.attach.toList
      let outcomes := moves.map (fun ⟨x, hx⟩ =>
        -- Take `x`: update current player's score and remove `x` from the set.
        let s_me' := s_me + x
        let remaining' := remaining.erase x

        if isFirstMove then
          -- First move rule (TeX item (1)):
          -- On the first move, `p1` must take exactly one element and then the turn passes.
          -- We therefore swap roles, evaluate from the opponent’s perspective, and negate
          -- to convert back to the current player's perspective.
          (valueAux remaining' s_opp s_me' false).neg
        else
          -- Subsequent move rule (TeX item (2)):
          -- On a turn, the current player must keep taking numbers while strictly behind,
          -- and stops as soon as they reach or exceed the opponent.
          if s_me' ≥ s_opp then
            -- We have caught up (or overtaken) on this pick: the turn ends and the opponent moves next.
            -- Swap players and negate to return to the current player's perspective.
            (valueAux remaining' s_opp s_me' false).neg
          else
            -- Still strictly behind after taking `x`: rules force us to continue the same turn,
            -- so the same player remains “current” in the recursive call.
            valueAux remaining' s_me' s_opp false
      )
      -- Optimal play: choose the best outcome among all legal next picks.
      Outcome.best outcomes
termination_by remaining.card
decreasing_by
  classical
  all_goals
    simpa [remaining'] using Finset.card_erase_lt_of_mem hx

/-- Public API: The game-theoretic value of Catch-Up on the set `S`, assuming optimal play.
    Returns `.win` if player 1 wins, `.loss` if player 2 wins, `.draw` if the game is tied. -/
noncomputable def value (S : Finset ℕ) : Outcome :=
  valueAux S 0 0 true


/-
Define helper function for the Catch-Up game on {1, ..., N}.
-/

noncomputable def catchUpValueN (N : ℕ) : Outcome :=
  value (Finset.Icc 1 N)

/--
Let \(T_N = \sum_{k=1}^{N} k = \frac{N(N+1)}{2}\).
If \(T_N\) is even (equivalently \(N \equiv 0 \pmod 4\) or \(N \equiv 3 \pmod 4\)),
then under optimal play the game `Catch-Up(\(\{1, \ldots, N\}\))` ends in a draw.
-/

@[category research open, AMS 91 11]
theorem value_of_even_mul_succ_self_div_two (N : ℕ) (h_even : Even (N * (N + 1) / 2)) :
    value (.Icc 1 N) = .draw := by
  sorry
end -- noncomputable section
end CatchUp
