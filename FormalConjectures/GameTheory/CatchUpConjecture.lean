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
  
/-
Formalization of the Catch-Up game and the conjecture.
We define the `Player`, `Position`, and `Outcome` types.
The main game logic is implemented in `value`, which recursively evaluates the game outcome under optimal play.
`catchUpValueN` defines the game value for the set {1, ..., N}.
The conjecture that the game ends in a draw when T_N is even is stated as `catchUp_draw_when_T_even`.

Reference:
----------
A. Isaksen, M. Ismail, S. J. Brams, A. Nealen,
"Catch-Up: A Game in Which the Lead Alternates,"
Game & Puzzle Design 1(2), 38–49, 2015.
https://game.engineering.nyu.edu/projects/catch-up/

Category and AMS classification:
--------------------------------
This is a research-level open problem in combinatorial game theory and number theory.
-/

import FormalConjectures.Util.ProblemImports

namespace CatchUp

noncomputable section
open scoped BigOperators

/-
Define Player and Position types for the Catch-Up game.
-/
inductive Player | P1 | P2
deriving DecidableEq, Repr

def Player.other : Player → Player
| P1 => P2
| P2 => P1

structure Position (S : Finset ℕ) where
  remaining : Finset ℕ
  s1 : ℕ
  s2 : ℕ
  turn : Player

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
exact Finset.card_lt_card ( Finset.erase_ssubset hx ); (
-- Since $x \in remaining$, removing $x$ from $remaining$ decreases its cardinality by one.
apply Finset.card_erase_lt_of_mem hx); (
-- Since $x \in \text{remaining}$, we have $\text{remaining.erase } x \subset \text{remaining}$, and thus $\text{remaining.erase } x.card < \text{remaining.card}$.
apply Finset.card_lt_card; exact Finset.erase_ssubset hx)

/-
Define helper functions for the Catch-Up game on {1, ..., N}.
-/
def initialSet (N : ℕ) : Finset ℕ :=
  (Finset.range N).image (· + 1)

noncomputable def catchUpValueN (N : ℕ) : Outcome :=
  value (initialSet N) 0 0 true

def T (N : ℕ) : ℕ := N * (N + 1) / 2

/-- English version:
"Let T N = 1 + 2 + ⋯ + N = N (N + 1) / 2.
If T N is even (equivalently N ≡ 0 or 3 mod 4),
then under optimal play the game Catch-Up({1,…,N}) ends in a draw."
-/
@[category research open, AMS 91 11]
theorem catchUp_draw_when_T_even (N : ℕ)
    (h_even : Even (T N)) :
    catchUpValueN N = Outcome.Draw := by
  sorry

end -- noncomputable section
end CatchUp
