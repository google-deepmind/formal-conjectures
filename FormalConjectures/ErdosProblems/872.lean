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

*Reference:* [erdosproblems.com/872](https://www.erdosproblems.com/872)

Consider the two-player game in which players alternately choose integers
from $\{2, 3, \ldots, n\}$ to be included in some set $A$ such that no $a \mid b$ for
$a \neq b \in A$ (i.e., $A$ remains a primitive set — an antichain under divisibility).
The game ends when no legal move is possible.

One player (the Lengthener) wants the game to last as long as possible;
the other (the Shortener) wants it to end quickly.

At least $\varepsilon n$ moves (for some $\varepsilon > 0$ and $n$ sufficiently large)?
At least $(1 - \varepsilon) n / 2$ moves (for any $\varepsilon > 0$ and $n$ sufficiently large)?

Erdős does not specify which player goes first, which may affect the answer.
This is a type of saturation game.

[Er92c] Erdős, P., _Some of my favourite problems in various branches of combinatorics_,
Matematiche (Catania) 47 (1992), 231–240.
-/

open Finset Classical

namespace Erdos872

/-- A finset of natural numbers is *primitive* (an antichain under divisibility)
if $a \mid b$ with $a, b \in A$ implies $a = b$. -/
def IsPrimitive (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ∣ b → a = b

/-- The universe of moves in the game: $\{2, 3, \ldots, n\}$. -/
def gameUniverse (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (· ≥ 2)

/-- Legal moves from a primitive position $A \subseteq \{2, \ldots, n\}$: elements $x$ in the
universe not in $A$ such that inserting $x$ keeps the set primitive. -/
noncomputable def legalMoves (n : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (gameUniverse n \ A).filter fun x =>
    ∀ a ∈ A, ¬(a ∣ x) ∧ ¬(x ∣ a)

/-- A legal strategy for the primitive-set game on $\{2, \ldots, n\}$: given any
game state with at least one legal move, it picks a legal move. -/
def LegalStrategy (n : ℕ) :=
  (A : Finset ℕ) → (legalMoves n A).Nonempty → {x // x ∈ legalMoves n A}

/-- Play the game with given legal strategies for the Lengthener and Shortener.
`lengthenerTurn = true` means it is the Lengthener's turn.
The `fuel` parameter bounds recursion depth ($n + 1$ suffices).
Returns the total number of moves played. -/
noncomputable def playGame (n : ℕ) (sL sS : LegalStrategy n) :
    ℕ → Finset ℕ → Bool → ℕ
  | 0, _, _ => 0
  | fuel + 1, A, lengthenerTurn =>
    if h : (legalMoves n A).Nonempty then
      let strategy := if lengthenerTurn then sL else sS
      let x := (strategy A h).val
      1 + playGame n sL sS fuel (insert x A) (!lengthenerTurn)
    else 0

/--
Erdős Problem 872 (weak form) [Er92c, p. 47]:

In the primitive-set saturation game on $\{2, 3, \ldots, n\}$, there exists $\varepsilon > 0$
such that, regardless of who moves first, the Lengthener can guarantee
at least $\varepsilon n$ moves for all sufficiently large $n$.
-/
@[category research open, AMS 5 91]
theorem erdos_872 :
    answer(sorry) ↔
    ∃ ε : ℝ, ε > 0 ∧
    ∃ N₀ : ℕ, ∀ n ≥ N₀,
      ∀ firstPlayer : Bool,
        ∃ sL : LegalStrategy n, ∀ sS : LegalStrategy n,
          (playGame n sL sS (n + 1) ∅ firstPlayer : ℝ) ≥ ε * (n : ℝ) := by
  sorry

/--
Erdős Problem 872 (strong form) [Er92c, p. 47]:

For every $\varepsilon > 0$ and all sufficiently large $n$, regardless of who moves first,
the Lengthener can guarantee at least $(1 - \varepsilon) \cdot n / 2$ moves in the
primitive-set saturation game on $\{2, 3, \ldots, n\}$.
-/
@[category research open, AMS 5 91]
theorem erdos_872.variants.strong :
    answer(sorry) ↔
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n ≥ N₀,
      ∀ firstPlayer : Bool,
        ∃ sL : LegalStrategy n, ∀ sS : LegalStrategy n,
          (playGame n sL sS (n + 1) ∅ firstPlayer : ℝ) ≥ (1 - ε) * (n : ℝ) / 2 := by
  sorry

end Erdos872
